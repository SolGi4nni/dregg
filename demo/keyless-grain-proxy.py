#!/usr/bin/env python3
# Serves play.html + proxies the grain API to the running agent-platform server (8903),
# AND provides a KEYLESS server-side brain: /keyless-drive runs an AWS Bedrock (Nova-Micro)
# Converse loop, proposing tool calls that are cap-gated/metered/receipted by the REAL dregg
# server via /act. The model is external (Bedrock); the enforcement + receipts are real dregg.
import http.server, socketserver, urllib.request, urllib.error, os, json
import boto3
ROOT="/Users/ember/dev/breadstuffs/site/grain"; UP="http://127.0.0.1:8903"; REGION="us-east-1"
MODEL=os.environ.get("BEDROCK_MODEL","us.amazon.nova-micro-v1:0")
PAGE={"/":"play.html","/play":"play.html","/play.html":"play.html","/dev":"index.html","/dev/":"index.html","/console":"index.html","/index.html":"index.html"}
BR=boto3.client("bedrock-runtime", region_name=REGION)
# The grain's fs tools (+ two the grain will REFUSE, so the model can try and get blocked).
TOOLSPEC={"tools":[
 {"toolSpec":{"name":"fs_write","description":"Write text to a file in the sandbox.","inputSchema":{"json":{"type":"object","properties":{"path":{"type":"string"},"content":{"type":"string"}},"required":["path","content"]}}}},
 {"toolSpec":{"name":"fs_read","description":"Read a file back from the sandbox.","inputSchema":{"json":{"type":"object","properties":{"path":{"type":"string"}},"required":["path"]}}}},
 {"toolSpec":{"name":"list_dir","description":"List files in the sandbox.","inputSchema":{"json":{"type":"object","properties":{"path":{"type":"string"}},"required":["path"]}}}},
 {"toolSpec":{"name":"http_get","description":"Fetch a web page over the internet.","inputSchema":{"json":{"type":"object","properties":{"url":{"type":"string"}},"required":["url"]}}}},
 {"toolSpec":{"name":"shell","description":"Run a shell command.","inputSchema":{"json":{"type":"object","properties":{"cmd":{"type":"string"}},"required":["cmd"]}}}},
]}
def act(host, subject, tool, args):
    body=json.dumps({"tool":tool,"args":args}).encode()
    req=urllib.request.Request(UP+"/act", data=body, method="POST")
    req.add_header("X-Dregg-Subject",subject); req.add_header("X-Dregg-Grain-Host",host); req.add_header("Content-Type","application/json")
    try:
        with urllib.request.urlopen(req, timeout=60) as r: return json.loads(r.read())
    except urllib.error.HTTPError as e: return {"http_error":e.code,"body":e.read().decode()[:200]}
def keyless_drive(goal, host, subject):
    steps=[]; msgs=[{"role":"user","content":[{"text":f"You are an AI agent driving a confined sandbox. Use ONLY tools to accomplish this goal, one at a time. Some tools may be BLOCKED by the sandbox — that is expected; adapt or stop. When done, reply with a short summary.\n\nGOAL: {goal}"}]}]
    for _ in range(8):
        try:
            r=BR.converse(modelId=MODEL, messages=msgs, toolConfig=TOOLSPEC, inferenceConfig={"maxTokens":400})
        except Exception as e:
            steps.append({"kind":"error","text":f"model error: {str(e)[:160]}"}); break
        content=r["output"]["message"]["content"]; msgs.append({"role":"assistant","content":content})
        tus=[c["toolUse"] for c in content if "toolUse" in c]
        if not tus:
            txt=" ".join(c.get("text","") for c in content if "text" in c).strip()
            if txt: steps.append({"kind":"say","text":txt})
            break
        tu=tus[0]; tool=tu["name"]; args=tu["input"]; res=act(host, subject, tool, args)
        admitted = res.get("admitted",0)>0
        steps.append({"kind":"act","tool":tool,"args":args,"admitted":admitted,
                      "cap_refused":res.get("cap_refused",0),"budget_refused":res.get("budget_refused",0),
                      "outcome":res.get("outcome"),"output":res.get("output"),
                      "receipt":res.get("receipt"),"consumed":res.get("consumed",0)})
        # feed the tool result back so the model observes (the OBSERVE half of the loop)
        tr = res.get("output") if admitted else f"BLOCKED by the sandbox: {res.get('outcome') or ('cap-refused' if res.get('cap_refused') else 'refused')}. This did not run."
        msgs.append({"role":"user","content":[{"toolResult":{"toolUseId":tu["toolUseId"],"content":[{"text":str(tr)[:600]}]}}]})
    return {"steps":steps,"model":MODEL}
class H(http.server.BaseHTTPRequestHandler):
    def _send(self,code,ct,body):
        self.send_response(code); self.send_header("Content-Type",ct); self.send_header("Content-Length",str(len(body))); self.end_headers(); self.wfile.write(body)
    def _page(self,fn):
        try: self._send(200,"text/html; charset=utf-8",open(os.path.join(ROOT,fn),"rb").read())
        except Exception as e: self._send(500,"text/plain",str(e).encode())
    def _proxy(self,method):
        p=self.path.split("?")[0]
        if p in PAGE: return self._page(PAGE[p])
        n=int(self.headers.get("Content-Length",0) or 0); data=self.rfile.read(n) if n else None
        if p=="/keyless-drive" and method=="POST":
            try:
                d=json.loads(data or b"{}"); out=keyless_drive(d.get("goal",""),d.get("host",""),d.get("subject",""))
                return self._send(200,"application/json",json.dumps(out).encode())
            except Exception as e: return self._send(500,"application/json",json.dumps({"error":str(e)[:200]}).encode())
        req=urllib.request.Request(UP+self.path,data=data,method=method)
        for h in ("X-Dregg-Subject","X-Dregg-Grain-Host","Content-Type","Accept"):
            v=self.headers.get(h);
            if v: req.add_header(h,v)
        try:
            with urllib.request.urlopen(req,timeout=180) as r: self._send(r.status,r.headers.get("Content-Type","application/json"),r.read())
        except urllib.error.HTTPError as e: self._send(e.code,e.headers.get("Content-Type","application/json"),e.read())
        except Exception as e: self._send(502,"text/plain",str(e).encode())
    def do_GET(self): self._proxy("GET")
    def do_POST(self): self._proxy("POST")
    def log_message(self,*a): pass
socketserver.ThreadingTCPServer.allow_reuse_address=True
with socketserver.ThreadingTCPServer(("127.0.0.1",8904),H) as s:
    print("grain proxy + Bedrock brain on :8904 (model",MODEL,")"); s.serve_forever()
