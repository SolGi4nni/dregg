#!/usr/bin/env python3
"""Fetch the consensus/crypto paper corpus into ./pdfs from pdfs/MANIFEST.json.

The PDFs are gitignored (76 MB, all publicly published). The manifest is the
source of truth: which paper, and which bytes.

  --verify   check existing files against their sha256 and report drift
  --missing  list papers with no recorded URL (they need one before a fresh
             clone can obtain them; several came from a private Zotero library)

⚠ A paper whose sha256 does not match the manifest is NOT the paper a reader lane
cited. Treat a mismatch as a finding, not as a stale hash to bump.
"""
import hashlib, json, os, sys, urllib.request

ROOT = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
PDFS = os.path.join(ROOT, "pdfs")
MAN = os.path.join(PDFS, "MANIFEST.json")

def digest(path):
    return hashlib.sha256(open(path, "rb").read()).hexdigest()

def main():
    papers = json.load(open(MAN))["papers"]
    verify, missing = "--verify" in sys.argv, "--missing" in sys.argv
    if missing:
        for p in papers:
            if not p["url"]:
                print(f"  NO URL  {p['file']}  ({p['source']})")
        return 0
    bad = fetched = 0
    for p in papers:
        dest = os.path.join(PDFS, p["file"])
        if os.path.exists(dest):
            if digest(dest) != p["sha256"]:
                print(f"  ⚠ DRIFT  {p['file']} — on disk differs from the manifest")
                bad += 1
            elif verify:
                print(f"  ok      {p['file']}")
            continue
        if verify:
            print(f"  MISSING {p['file']}")
            bad += 1
            continue
        if not p["url"]:
            print(f"  NO URL  {p['file']} — cannot fetch; see --missing")
            bad += 1
            continue
        try:
            req = urllib.request.Request(p["url"], headers={"User-Agent": "Mozilla/5.0"})
            data = urllib.request.urlopen(req, timeout=90).read()
        except Exception as exc:
            print(f"  FAIL    {p['file']}: {exc}")
            bad += 1
            continue
        got = hashlib.sha256(data).hexdigest()
        if got != p["sha256"]:
            # Publishers do re-typeset. Refuse rather than silently accept a
            # different document under a cited filename.
            print(f"  ⚠ HASH   {p['file']} — fetched bytes differ from the manifest; NOT written")
            bad += 1
            continue
        open(dest, "wb").write(data)
        fetched += 1
        print(f"  got     {p['file']}")
    print(f"\n  {fetched} fetched, {bad} problem(s), {len(papers)} in manifest")
    return 1 if bad else 0

if __name__ == "__main__":
    sys.exit(main())
