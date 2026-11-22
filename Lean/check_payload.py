"""Compare the certificate printed in the PDF with the supplied data and checker."""

import argparse
import base64
import binascii
from pathlib import Path
import re
import subprocess
import zlib


ROOT = Path(__file__).resolve().parent


def printed_payload(text):
    records = re.findall(r"(?m)^ *D([0-9]{3}) +([A-Za-z0-9+/=]+) *$", text)
    if [int(number) for number, _ in records] != list(range(111)):
        raise SystemExit("Missing or out-of-order data records in the printed appendix.")
    try:
        encoded = "".join(chunk for _, chunk in records)
        return zlib.decompress(base64.b64decode(encoded, validate=True))
    except (binascii.Error, zlib.error) as error:
        raise SystemExit(f"Invalid compressed appendix data: {error}") from error


def printed_checker(text):
    lines = []
    for number, indent, content in re.findall(r"(?m)^ *P([0-9]{3})/([0-9]+) +(.+)$", text):
        index = int(number) - 1
        if index < len(lines):
            raise SystemExit("Repeated or out-of-order program lines in the printed appendix.")
        lines.extend([""] * (index - len(lines)))
        lines.append(" " * int(indent) + content.rstrip())
    if not lines:
        raise SystemExit("No program lines found in the printed appendix.")
    return ("\n".join(lines) + "\n").encode("utf-8")


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("pdf", type=Path, nargs="?",
                        default=ROOT.parent / "Elections with Condorcet Dimension 4.pdf")
    parser.add_argument("--checker", type=Path, help="also compare the printed Python source to this file")
    parser.add_argument("--pdftotext", default="pdftotext", help="path to the Poppler executable")
    args = parser.parse_args()

    text = subprocess.check_output([args.pdftotext, "-layout", str(args.pdf), "-"], encoding="utf-8")
    payload = printed_payload(text)
    if payload != (ROOT / "pair-menus.json").read_bytes():
        raise SystemExit("The PDF data differ from the JSON input used by Lean.")
    if args.checker is not None:
        if printed_checker(text) != args.checker.read_bytes():
            raise SystemExit("The Python source printed in the PDF differs from the supplied checker.")
        print("The Python checker matches the printed program byte for byte.")
    print(f"All {len(payload):,} bytes of the Lean input match the PDF.")


if __name__ == "__main__":
    main()
