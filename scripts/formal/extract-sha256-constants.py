#!/usr/bin/env python3
"""Copy complete SHA-256 constants from the pinned sha2 0.10.9 source."""
import argparse
import hashlib
from pathlib import Path
import re


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument("source", type=Path)
    parser.add_argument("destination", type=Path)
    args = parser.parse_args()
    raw = args.source.read_bytes()
    source = raw.decode()
    output = ["{-# OPTIONS --safe #-}\n",
              "-- Complete algorithm constants from sha2 0.10.9, copied by\n",
              "-- scripts/formal/extract-sha256-constants.py.\n",
              f"-- consts.rs SHA-256: {hashlib.sha256(raw).hexdigest()}\n",
              "module Mimir.SHA256Constants where\n\n",
              "open import Data.Nat using (ℕ)\n",
              "open import Data.Vec using (Vec; []; _∷_)\n\n"]
    for name, agda_name, size in [("K32", "roundConstants", 64), ("H256_256", "initialState", 8)]:
        body = re.search(rf"pub const {name}:.*?= \[(.*?)\];", source, re.S).group(1)
        values = [int(x, 16) for x in re.findall(r"0x[0-9a-fA-F]+", body)]
        assert len(values) == size
        output += [f"{agda_name} : Vec ℕ {size}\n", f"{agda_name} =\n"]
        for start in range(0, size, 4):
            output.append("  " + " ∷ ".join(map(str, values[start:start + 4])) + " ∷\n")
        output.append("  []\n\n")
        print(f"{name}: {len(values)} constants")
    args.destination.write_text("".join(output))
    print(f"source_sha256={hashlib.sha256(raw).hexdigest()}")


if __name__ == "__main__":
    main()
