"""Fetch candidate images for glossary entries from Wikipedia / Wikimedia Commons.

One-shot curation tool, not part of the build. For each (slug, Wikipedia title) pair
below it asks the Wikipedia REST summary API for the page's lead image, asks the
Commons API for that file's licence and attribution, keeps only files that are free
to reuse (public domain, CC0, CC BY, CC BY-SA; shared repository, never a local
non-free upload), downloads a thumbnail into docs/img/<slug>.<ext>, and writes a
review sheet (scratch, not committed) listing what it found. A human then looks at
every image before the `image:` block goes into docs/glossary.yaml, because an
eponym has namesakes and a wrong portrait is worse than none.

Usage:  python scripts/lib/glossary_images.py <review-dir>
"""
import json
import os
import re
import sys
import time
import urllib.parse

import requests

UA = "csd-glossary-images/1.0 (https://constraintsurfacedynamics.com; zblore@gmail.com)"
S = requests.Session()
S.headers["User-Agent"] = UA

# slug -> Wikipedia article whose lead image is the candidate. Portraits for eponyms,
# diagrams for concepts, nothing for programme-internal terms (they have no page).
MAP = {
    "fubini-study-measure": "Guido Fubini",
    "born-weight": "Max Born",
    "duistermaat-heckman": "Hans Duistermaat",
    "gleason-theorem": "Andrew M. Gleason",
    "wigner-rigidity": "Eugene Wigner",
    "stone-theorem": "Marshall H. Stone",
    "bell-chsh": "John Stewart Bell",
    "ghz-state": "Anton Zeilinger",
    "tsirelson-bound": "Boris Tsirelson",
    "landauer-principle": "Rolf Landauer",
    "jarzynski-equality": "Christopher Jarzynski",
    "crooks-fluctuation-theorem": "Gavin E. Crooks",
    "von-neumann-entropy": "John von Neumann",
    "liouville-measure": "Joseph Liouville",
    "kahler-form": "Erich Kähler",
    "luders-rule": "Gerhart Lüders",
    "naimark-dilation": "Mark Naimark",
    "bargmann": "Valentine Bargmann",
    "bloch-sphere": "Bloch sphere",
    "borel-set": "Émile Borel",
    "cglmp-inequality": "Nicolas Gisin",
    "deutsch-jozsa": "David Deutsch",
    "dirichlet-distribution": "Peter Gustav Lejeune Dirichlet",
    "elitzur-vaidman": "Elitzur–Vaidman bomb tester",
    "euclidean-space": "Euclid",
    "fisher-information": "Ronald Fisher",
    "gibbs-state": "Josiah Willard Gibbs",
    "gisin-theorem": "Nicolas Gisin",
    "grover-algorithm": "Lov Grover",
    "haar-measure": "Alfréd Haar",
    "hermitian-operator": "Charles Hermite",
    "hilbert-space": "David Hilbert",
    "hong-ou-mandel": "Hong–Ou–Mandel effect",
    "jacobi-identity": "Carl Gustav Jacob Jacobi",
    "kronecker-product": "Leopold Kronecker",
    "leggett-garg": "Anthony James Leggett",
    "loewner-order": "Charles Loewner",
    "mach-zehnder": "Mach–Zehnder interferometer",
    "malus-law": "Étienne-Louis Malus",
    "mermin-inequality": "N. David Mermin",
    "pauli-matrices": "Wolfgang Pauli",
    "peres-criterion": "Asher Peres",
    "poisson-bracket": "Siméon Denis Poisson",
    "ramsey-interferometry": "Norman Ramsey",
    "schrodinger-equation": "Erwin Schrödinger",
    "shor-algorithm": "Peter Shor",
    "stern-gerlach": "Stern–Gerlach experiment",
    "kochen-specker": "Ernst Specker",
    "copenhagen": "Niels Bohr",
    "many-worlds": "Hugh Everett III",
    "bohmian-mechanics": "David Bohm",
    "measurement-problem": "Schrödinger's cat",
    "fibre": "Fiber bundle",
    "lieb-robinson-bound": "Elliott H. Lieb",
    "wick-theorem": "Gian Carlo Wick",
    "kms-condition": "Ryogo Kubo",
    "lindblad-equation": "Göran Lindblad",
    "lie-trotter-formula": "Sophus Lie",
    "choi-theorem": "Man-Duen Choi",
    "robertson-uncertainty": "Howard P. Robertson",
    "ozawa-error-disturbance": "Masanao Ozawa",
    "quantum-fourier-transform": "Joseph Fourier",
    "bernstein-vazirani": "Umesh Vazirani",
    "amplitude-amplification": "Gilles Brassard",
    "amplitude-estimation": "Michele Mosca",
    "gottesman-knill": "Daniel Gottesman",
    "steane-code": "Andrew Steane",
    "magic-state": "Alexei Kitaev",
    "holevo-bound": "Alexander Holevo",
    "klein-inequality": "Oskar Klein",
    "hadamard-test": "Jacques Hadamard",
    "shor-code": "Peter Shor",
    "simon-algorithm": "Daniel Simon (computer scientist)",
    "phase-estimation": "Alexei Kitaev",
    "hidden-variables": "Louis de Broglie",
    "spontaneous-collapse": "GianCarlo Ghirardi",
    "contextuality": "Ernst Specker",
    "determinism": "Pierre-Simon Laplace",
    "typicality": "Ludwig Boltzmann",
    "canonical-typicality": "Ludwig Boltzmann",
    "no-signalling": "Albert Einstein",
    "quantum-channel": "Claude Shannon",
    "entropy-subadditivity": "Claude Shannon",
    "stinespring-dilation": "Mark Naimark",
    "collapse": "Werner Heisenberg",
    "qbism": "Thomas Bayes",
}

# Second choices, tried when the first title has no usable lead image: a concept page's
# diagram where the person has no free portrait.
ALT = {
    "grover-algorithm": "Grover's algorithm",
    "many-worlds": "Many-worlds interpretation",
    "steane-code": "Steane code",
    "robertson-uncertainty": "Uncertainty principle",
    "phase-estimation": "Quantum phase estimation algorithm",
    "simon-algorithm": "Simon's problem",
    "bernstein-vazirani": "Bernstein–Vazirani algorithm",
    "magic-state": "Magic state distillation",
    "gottesman-knill": "Gottesman–Knill theorem",
    "lindblad-equation": "Lindbladian",
    "choi-theorem": "Choi's theorem on completely positive maps",
    "jarzynski-equality": "Jarzynski equality",
    "crooks-fluctuation-theorem": "Crooks fluctuation theorem",
    "duistermaat-heckman": "Duistermaat–Heckman formula",
    "spontaneous-collapse": "Objective-collapse theory",
    "hong-ou-mandel": "Beam splitter",
    "fibre": "Fiber bundle",
    "wick-theorem": "Wick's theorem",
    "kms-condition": "KMS state",
    "loewner-order": "Loewner order",
    "ozawa-error-disturbance": "Uncertainty principle",
    "amplitude-estimation": "Quantum counting algorithm",
    "naimark-dilation": "Naimark's dilation theorem",
    "stinespring-dilation": "Stinespring dilation theorem",
    "luders-rule": "Measurement in quantum mechanics",
    "bargmann": "Bargmann's theorem",
}

# Explicit Commons files, for pages whose lead image is absent or wrong but which carry
# the right figure further down.
FILES = {
    "hong-ou-mandel": ("Hong Ou Mandel effect.png", "Hong–Ou–Mandel effect"),
    "grover-algorithm": ("Grovers algorithm geometry.png", "Grover's algorithm"),
    "fibre": ("Moebius Surface 1 Display Small.png", "Fiber bundle"),
    "phase-estimation": ("PhaseCircuit.svg", "Quantum phase estimation algorithm"),
}

# Licences that permit reuse with a credit line. GFDL-only files are left out: reuse
# would mean shipping the licence text with the page.
FREE = re.compile(
    r"^(public domain|pd(-.*)?|cc0.*|cc by(-sa)?( \d(\.\d)?( [a-z]{2})?)?|cc-by(-sa)?(-\d\.\d)?|"
    r"attribution|copyrighted free use|no restrictions)$", re.I)


def summary(title):
    r = S.get("https://en.wikipedia.org/api/rest_v1/page/summary/"
              + urllib.parse.quote(title.replace(" ", "_")), timeout=30)
    if r.status_code != 200:
        return None
    return r.json()


def commons_info(filename):
    """Licence, artist and a 640px thumbnail URL for File:<filename> on Commons."""
    r = S.get("https://commons.wikimedia.org/w/api.php", params={
        "action": "query", "titles": "File:" + filename, "prop": "imageinfo",
        "iiprop": "extmetadata|url|mime", "iiurlwidth": "480", "format": "json"}, timeout=30)
    pages = r.json().get("query", {}).get("pages", {})
    for _, p in pages.items():
        if "imageinfo" not in p:
            return None
        ii = p["imageinfo"][0]
        md = ii.get("extmetadata", {})
        g = lambda k: re.sub(r"<[^>]+>", "", md.get(k, {}).get("value", "")).strip()
        return {
            "licence": g("LicenseShortName"), "licence_url": g("LicenseUrl"),
            "artist": g("Artist"), "credit": g("Credit"), "attribution": g("Attribution"),
            "thumb": ii.get("thumburl"), "url": ii.get("url"), "mime": ii.get("mime"),
            "page": "https://commons.wikimedia.org/wiki/File:" + filename.replace(" ", "_"),
        }
    return None


def main(outdir):
    os.makedirs(outdir, exist_ok=True)
    os.makedirs("docs/img", exist_ok=True)
    sheet = []
    def attempt(slug, title):
        time.sleep(0.2)
        row = {"slug": slug, "title": title}
        sm = summary(title)
        if not sm or "originalimage" not in sm:
            row["status"] = "no lead image"
            return row
        src = sm["originalimage"]["source"]
        m = re.search(r"/commons/(?:thumb/)?[0-9a-f]/[0-9a-f]{2}/([^/?]+)", src)
        if not m:
            row["status"] = "not on Commons: " + src
            return row
        fname = urllib.parse.unquote(m.group(1))
        ci = commons_info(fname)
        if not ci:
            row["status"] = "no Commons record for " + fname
            return row
        row.update(ci)
        row["file"] = fname
        row["article"] = sm.get("content_urls", {}).get("desktop", {}).get("page")
        row["extract"] = sm.get("extract", "")[:160]
        if not FREE.match(ci["licence"] or ""):
            row["status"] = "licence not free: " + (ci["licence"] or "?")
            return row
        thumb = ci["thumb"] or ci["url"]
        # Commons renders SVG thumbnails as PNG; GIF and PNG thumbnails keep their type.
        ext = {"image/jpeg": ".jpg", "image/png": ".png", "image/svg+xml": ".png",
               "image/gif": ".gif"}.get(ci["mime"], os.path.splitext(fname)[1].lower())
        dest = os.path.join("docs/img", slug + ext)
        img = S.get(thumb, timeout=60)
        if img.status_code != 200:
            row["status"] = "download failed " + str(img.status_code)
            return row
        open(dest, "wb").write(img.content)
        row["dest"] = dest
        row["bytes"] = len(img.content)
        row["status"] = "ok"
        print(f"{slug:32s} ok  {ci['licence']:16s} {fname[:60]}")
        return row

    def attempt_file(slug, fname, title):
        time.sleep(0.2)
        row = {"slug": slug, "title": title, "file": fname,
               "article": "https://en.wikipedia.org/wiki/" + title.replace(" ", "_")}
        ci = commons_info(fname)
        if not ci:
            row["status"] = "no Commons record for " + fname
            return row
        row.update(ci)
        if not FREE.match(ci["licence"] or ""):
            row["status"] = "licence not free: " + (ci["licence"] or "?")
            return row
        ext = {"image/jpeg": ".jpg", "image/png": ".png", "image/svg+xml": ".png",
               "image/gif": ".gif"}.get(ci["mime"], os.path.splitext(fname)[1].lower())
        dest = os.path.join("docs/img", slug + ext)
        img = S.get(ci["thumb"] or ci["url"], timeout=60)
        if img.status_code != 200:
            row["status"] = "download failed " + str(img.status_code)
            return row
        open(dest, "wb").write(img.content)
        row["dest"], row["bytes"], row["status"] = dest, len(img.content), "ok"
        print(f"{slug:32s} ok  {ci['licence']:16s} {fname[:60]}  (explicit file)")
        return row

    for slug, title in MAP.items():
        if slug in FILES:
            sheet.append(attempt_file(slug, *FILES[slug]))
            continue
        row = attempt(slug, title)
        if row["status"] != "ok" and slug in ALT:
            row2 = attempt(slug, ALT[slug])
            row2["first_try"] = row["status"]
            row = row2
        sheet.append(row)
    json.dump(sheet, open(os.path.join(outdir, "sheet.json"), "w", encoding="utf-8"),
              indent=1, ensure_ascii=False)
    print("rows:", len(sheet), "ok:", sum(1 for r in sheet if r["status"] == "ok"))


if __name__ == "__main__":
    main(sys.argv[1])
