#!/usr/bin/env python3
"""Deep literature search via Kagi, for filling the corpus in ./pdfs.

WHY THIS EXISTS: on 2026-08-08 we were reasoning about our own consensus rule from
the implementation outward, with THREE papers on disk and none of them about
consensus. A lane then concluded "no paper treats BFT committee growth at all" —
from a corpus that contained no reconfiguration literature. It was wrong, and the
construction we needed (Duan & Zhang, Foundations of Dynamic BFT) had been sitting
in ember's Zotero the whole time.

  ⚑ A NEGATIVE CLAIM ABOUT THE LITERATURE IS ONLY AS GOOD AS THE CORPUS SEARCHED.
    If you conclude something is unstudied, say which sources you searched.

Key: KAGI_API_KEY from ~/dev/allgame/.env (v1 endpoint; v0 is legacy prepaid).
Usage:  python3 scripts/lit-search.py "query one" "query two"
"""
import json, os, sys, urllib.request

def _key():
    env = os.path.expanduser("~/dev/allgame/.env")
    if os.environ.get("KAGI_API_KEY"):
        return os.environ["KAGI_API_KEY"]
    for line in open(env):
        if line.startswith("KAGI_API_KEY="):
            return line.split("=", 1)[1].strip().strip("\"'")
    sys.exit("KAGI_API_KEY not found (env or ~/dev/allgame/.env)")

def search(query, limit=10):
    req = urllib.request.Request(
        "https://kagi.com/api/v1/search",
        data=json.dumps({"query": query}).encode(),
        headers={"Authorization": f"Bearer {_key()}", "Content-Type": "application/json"},
        method="POST")
    try:
        payload = json.loads(urllib.request.urlopen(req, timeout=25).read())
    except Exception as exc:                       # network, auth, rate limit
        print(f"  ERROR: {exc}", file=sys.stderr)
        return []
    # t==1 rows are Kagi's "related searches", not results.
    return [(i.get("title", ""), i.get("url", ""), (i.get("snippet") or "")[:160])
            for i in (payload.get("data") or {}).get("search", [])[:limit]
            if i.get("t") != 1]

if __name__ == "__main__":
    if len(sys.argv) < 2:
        sys.exit(__doc__)
    for q in sys.argv[1:]:
        print(f"\n### {q}")
        for title, url, snippet in search(q):
            print(f"  {title[:88]}\n    {url}")
            if snippet:
                print(f"    {snippet[:120]}")
