"""Generate the published CSD glossary from docs/glossary.yaml.

Output goes to docs/_site/ and is NOT committed. Actions builds it on push and
hands it to Pages. Committing generated HTML lets the site and the source
disagree, which is the failure this whole layer exists to prevent.

Emits: index.html, <slug>/index.html (one entry per URL, because the citable unit
is the entry and AI search cites passages), sitemap.xml, llms.txt, CNAME, and
GLOSSARY.md at the repo root as the committed index layer. Each entry page
carries schema.org DefinedTerm inside a DefinedTermSet.

Layout intent: the hook carries the claim and comes first, because a reference
page that opens with a category label is a page nobody reads. The three registers
descend in register rather than sitting as three equal grey blocks, and the
provenance strip is promoted to the top: "this is proved, here is the line" is
part of the interest, not administrative trailing matter.
"""
import html
import json
import os
import re
import shutil

import yaml

d = yaml.safe_load(open("docs/glossary.yaml", encoding="utf-8"))
meta, entries = d["meta"], d["entries"]

# Presentation order is ALPHABETICAL and is decided here, not in the source file.
# glossary.yaml stays in whatever order entries were written, because a source file
# that must be kept sorted by hand is a source file that will not be. Sorting is a
# render concern. Case- and accent-insensitive on the term, so "von Neumann" files
# under v and "Kahler" under k, next to where a reader will look for them.
def _sortkey(e):
    t = (e.get("term") or e.get("slug") or "").lower()
    for a, b in (("ä", "a"), ("ö", "o"), ("ü", "u"), ("é", "e"), ("è", "e")):
        t = t.replace(a, b)
    return t

entries = sorted(entries, key=_sortkey)
SITE, REPO, SHA = meta["site"].rstrip("/"), meta["repo"].rstrip("/"), meta["sha"]
# The programme's front door. Every outward link to the main site reads from this
# one field; nothing below hardcodes the domain.
SITE_MAIN = meta["site_main"].rstrip("/")
REFS = d.get("refs") or {}
OUT = "docs/_site"
shutil.rmtree(OUT, ignore_errors=True)
os.makedirs(OUT, exist_ok=True)
E = html.escape

# --- automatic cross-referencing -------------------------------------------
# Every named thing in the prose gets linked once, without the author marking it
# up. Terms naming another entry resolve internally; everything else resolves to
# the external registry. Longest match wins, so "Fubini-Study metric" is not eaten
# by "Fubini". An entry never links to itself, and only the first occurrence on a
# page is linked, because a paragraph of blue is harder to read than one of black.
LINKS = {}
for _e in entries:
    for _k in [_e["term"]] + list(_e.get("eponyms") or []):
        LINKS.setdefault(_k.lower(), (SITE + "/" + _e["slug"] + "/", None, _e["slug"]))
for _k, _v in REFS.items():
    LINKS.setdefault(_k.lower(), (_v["url"], _v.get("source"), None))

_PAT = re.compile(
    r"\b(" + "|".join(re.escape(k) for k in sorted(LINKS, key=len, reverse=True)) + r")\b",
    re.I,
) if LINKS else None


def linkify(text, self_slug, used, sources):
    """Escape, then link the first occurrence of each known term. Single pass, so
    inserted markup is never rescanned.

    Paragraphs: a blank line in the YAML folded scalar arrives as a newline in the
    parsed value. Render each as its own <p> block (the caller wraps the whole
    return in one <p>...</p>, so the joiner closes and reopens). Before 2026-08-19
    this function collapsed ALL whitespace, which made paragraphs impossible to
    write no matter what the source did -- long registers rendered as one wall."""
    paras = [p for p in re.split(r"\n+", text.strip()) if p.strip()]
    if not paras:
        return ""

    def _one(ptext):
        esc = E(" ".join(ptext.split()))
        if not _PAT:
            return esc
        return _PAT.sub(sub, esc)

    if not _PAT:
        return "</p><p>".join(E(" ".join(p.split())) for p in paras)

    def sub(m):
        key = m.group(1).lower()
        url, source, slug = LINKS[key]
        if key in used or slug == self_slug:
            return m.group(0)
        used.add(key)
        if source:
            sources[source] = url
        cls = "" if slug else ' class="ext"'
        return '<a href="' + url + '"' + cls + ">" + m.group(0) + "</a>"

    return "</p><p>".join(_one(p) for p in paras)

CSS = (
    "*{box-sizing:border-box}"
    ":root{--bg:#fdfdfc;--fg:#16171a;--mut:#63666d;--faint:#8a8d94;--line:#e4e3df;"
    "--acc:#8a3324;--card:#f4f3ef;--code:#2b2d31}"
    "@media(prefers-color-scheme:dark){:root:not([data-theme=light]){--bg:#141416;"
    "--fg:#e9e8e4;--mut:#a2a5ac;--faint:#7e828a;--line:#2b2b2f;--acc:#e08a72;"
    "--card:#1d1d20;--code:#c9cbd1}}"
    ":root[data-theme=dark]{--bg:#141416;--fg:#e9e8e4;--mut:#a2a5ac;--faint:#7e828a;"
    "--line:#2b2b2f;--acc:#e08a72;--card:#1d1d20;--code:#c9cbd1}"
    "body{margin:0;background:var(--bg);color:var(--fg);"
    "font:400 17px/1.7 Georgia,'Iowan Old Style','Palatino Linotype',serif;"
    "-webkit-font-smoothing:antialiased}"
    ".w{max-width:38rem;margin:0 auto;padding:3rem 1.35rem 5rem}"
    "a{color:var(--acc);text-underline-offset:2px}"
    ".sans{font-family:-apple-system,BlinkMacSystemFont,'Segoe UI',Helvetica,Arial,sans-serif}"
    ".crumb{font:500 .72rem/1 -apple-system,BlinkMacSystemFont,'Segoe UI',sans-serif;"
    "letter-spacing:.13em;text-transform:uppercase;color:var(--faint);"
    "display:block;margin-bottom:2.6rem}"
    ".crumb a{color:var(--faint);text-decoration:none}"
    ".crumb a:hover{color:var(--acc)}"
    ".crumb .sep{margin:0 .5em;color:var(--line)}"
    ".orient{font:400 .95rem/1.65 -apple-system,BlinkMacSystemFont,'Segoe UI',sans-serif;"
    "color:var(--mut);margin:-.9rem 0 2.6rem}"
    "h1{font-size:2.05rem;line-height:1.15;letter-spacing:-.015em;margin:0 0 1.4rem;"
    "font-weight:400}"
    ".hook{font-size:1.3rem;line-height:1.45;color:var(--fg);margin:0 0 1.9rem;"
    "padding-left:1.05rem;border-left:3px solid var(--acc)}"
    ".strip{display:flex;flex-wrap:wrap;gap:.45rem;margin:0 0 3.2rem;"
    "padding-bottom:2rem;border-bottom:1px solid var(--line)}"
    ".chip{font:500 .73rem/1 -apple-system,BlinkMacSystemFont,'Segoe UI',sans-serif;"
    "letter-spacing:.04em;background:var(--card);border:1px solid var(--line);"
    "color:var(--mut);padding:.4rem .62rem;border-radius:4px;text-decoration:none}"
    "a.chip:hover{border-color:var(--acc);color:var(--acc)}"
    ".chip b{font-weight:600;color:var(--fg)}"
    "h2{font:600 .7rem/1 -apple-system,BlinkMacSystemFont,'Segoe UI',sans-serif;"
    "letter-spacing:.15em;text-transform:uppercase;color:var(--faint);"
    "margin:0 0 .85rem}"
    "section{margin:0 0 2.9rem}"
    ".r1 p{font-size:1.12rem;line-height:1.72;margin:0}"
    ".r2 p{margin:0}"
    ".r3{background:var(--card);border:1px solid var(--line);border-radius:6px;"
    "padding:1.3rem 1.4rem}"
    ".r3 p{margin:0;font-size:.97rem;line-height:1.66;color:var(--mut)}"
    ".r3 h2{margin-bottom:.7rem}"
    "code{font-family:ui-monospace,SFMono-Regular,Menlo,monospace;font-size:.85em;"
    "color:var(--code)}"
    ".foot{border-top:1px solid var(--line);padding-top:1.6rem;margin-top:3.4rem;"
    "font:400 .88rem/1.65 -apple-system,BlinkMacSystemFont,'Segoe UI',sans-serif;"
    "color:var(--mut)}"
    ".foot dl{display:grid;grid-template-columns:6.5rem 1fr;gap:.5rem 1rem;margin:0}"
    ".foot dt{color:var(--faint);font-size:.78rem;letter-spacing:.06em;"
    "text-transform:uppercase;padding-top:.15rem}"
    ".foot dd{margin:0}"
    "a.ext{background-image:linear-gradient(var(--faint),var(--faint));background-size:100% 1px;background-repeat:no-repeat;background-position:0 1.15em;text-decoration:none}a.ext:hover{background-image:linear-gradient(var(--acc),var(--acc))}"
    ".note{margin-top:2rem;font-size:.8rem;color:var(--faint);line-height:1.6}"
    ".ck{position:fixed;left:0;right:0;bottom:0;z-index:50;background:var(--card);"
    "border-top:1px solid var(--line);"
    "font:400 .82rem/1.55 -apple-system,BlinkMacSystemFont,'Segoe UI',sans-serif;"
    "color:var(--mut)}"
    ".ck[hidden]{display:none}"
    ".ck .in{max-width:38rem;margin:0 auto;padding:.9rem 1.35rem;display:flex;"
    "gap:1.1rem;align-items:center;justify-content:space-between}"
    ".ck p{margin:0}"
    ".ck button{flex:none;font:500 .8rem/1 -apple-system,BlinkMacSystemFont,"
    "'Segoe UI',sans-serif;color:var(--bg);background:var(--acc);border:0;"
    "border-radius:5px;padding:.6rem 1rem;cursor:pointer}"
    ".ck button:hover{opacity:.87}"
    "@media(max-width:32rem){.ck .in{flex-direction:column;align-items:flex-start;"
    "gap:.7rem}}"
    "ul.idx{list-style:none;padding:0;margin:0}"
    "ul.idx li{border-bottom:1px solid var(--line);padding:1.15rem 0}"
    "ul.idx a{text-decoration:none}"
    "ul.idx .t{font-size:1.2rem;display:block;margin-bottom:.3rem}"
    "ul.idx .h{color:var(--mut);font-size:.95rem;line-height:1.6}"
    "ul.idx a:hover .t{color:var(--acc)}"
    "@media(max-width:32rem){h1{font-size:1.72rem}.hook{font-size:1.15rem}"
    ".foot dl{grid-template-columns:1fr;gap:.15rem}"
    ".foot dt{padding-top:.6rem}}"
)


GA_ID = "G-W92F78PH51"

# Google Analytics, and the disclosure that goes with it. GA4 sets first-party
# cookies (`_ga`, `_ga_<id>`), so the notice is not optional decoration -- it
# rides in `page()` rather than in any one builder so that every generated page
# carries it, including ones added later.
ANALYTICS = (
    '<script async src="https://www.googletagmanager.com/gtag/js?id=' + GA_ID + '"></script>'
    '<script>window.dataLayer=window.dataLayer||[];'
    "function gtag(){dataLayer.push(arguments);}"
    'gtag("js",new Date());gtag("config","' + GA_ID + '");</script>'
)

# A dismissible banner, and the markup ships it `hidden`: script reveals it, so
# with JavaScript off it never appears -- which is the correct coupling rather
# than an oversight, because with JavaScript off `gtag` never runs either, no
# cookies are set, and there is nothing to disclose. The same reasoning is why
# the banner cannot strand a reader: if the reveal never runs it stays out of
# the way instead of covering the page forever.
#
# Every `localStorage` access is guarded. A browser that blocks site data throws
# on read, and the catch leaves the banner shown rather than crashing the page.
# The glossary is served as its own site, so the main site's footer does not reach
# these pages and the policy has to be linked from here. It rides in `page()`
# alongside the banner so every generated page carries it -- and unlike the banner
# it is permanent, because a dismissed notice must not take the policy link with it.
PRIVACY_LINE = (
    '<p class="note privacy"><a class="ext"'
    ' href="https://www.constraintsurfacedynamics.com/privacy">Privacy policy</a></p>'
)

COOKIE_BANNER = (
    '<div class="ck" id="ck" hidden><div class="in">'
    "<p>Google Analytics counts visits to this page, which stores cookies in your browser. "
    "They record how the page was reached, not who you are, and nothing is passed on. "
    "Blocking cookies for this site breaks nothing here."
    ' <a class="ext" href="https://policies.google.com/technologies/cookies"'
    ' rel="noopener nofollow">Details</a>.</p>'
    '<button type="button" id="ckb">Got it</button>'
    "</div></div>"
    '<script>(function(){var k="csd-cookie-ack",e=document.getElementById("ck");'
    "if(!e)return;var d=false;"
    'try{d=localStorage.getItem(k)==="1"}catch(x){}'
    "if(!d)e.hidden=false;"
    'var b=document.getElementById("ckb");'
    "if(b)b.addEventListener(\"click\",function(){e.hidden=true;"
    'try{localStorage.setItem(k,"1")}catch(x){}});})();</script>'
)


def page(title, desc, body, jsonld, canon):
    return (
        '<!doctype html><html lang="en"><head><meta charset="utf-8">'
        '<meta name="viewport" content="width=device-width,initial-scale=1">'
        + "<title>" + E(title) + "</title>"
        + '<meta name="description" content="' + E(desc) + '">'
        + '<link rel="canonical" href="' + canon + '">'
        + "<style>" + CSS + "</style>"
        + '<script type="application/ld+json">' + jsonld + "</script>"
        + ANALYTICS
        + '</head><body><div class="w">' + body + PRIVACY_LINE + "</div>"
        + COOKIE_BANNER
        + "</body></html>"
    )


def thm_line(mod, thm):
    """Line number of a declaration, so the source link is a precise permalink."""
    if not (mod and thm and os.path.isfile(mod)):
        return None
    pat = re.compile(r"\s*(public\s+)?(theorem|lemma|def|abbrev)\s+" + re.escape(thm) + r"\b")
    for i, line in enumerate(open(mod, encoding="utf-8", errors="replace"), 1):
        if pat.match(line):
            return i
    return None


STATUS_GLOSS = {
    "proved-in-corpus": "proved here, no imported axioms",
    "standard-mathematics": "standard mathematics, cited outward",
    "imported-result": "imported, not proved here",
    "physical-postulate": "postulate, carried as a hypothesis",
    "definition": "a definition, no claim attached",
    "open": "named, not settled",
}

# One line, on every page, below the existing note: where this glossary belongs
# and where the proofs live. Deliberately not a nav bar and not a call to action.
SITE_LINE = ('<p class="note">Part of <a href="' + SITE_MAIN
             + '/">Constraint-Surface Dynamics</a> &middot; Formalised in '
             + '<a href="' + REPO + '">csd-lean4</a>.</p>')

idx_items, q_items, sitemap, llms, md = [], [], [SITE + "/"], [], []

for e in entries:
    slug, term, st = e["slug"], e["term"], e["status"]
    # kind: "question" switches the page from a DefinedTerm to an FAQ answer.
    # Question pages are argumentative rather than definitional: they carry
    # FAQPage schema, answer-shaped section headings, and no status chip (the
    # controlled status vocabulary describes claims, and a question page's
    # claims live in the theorem pages it links). They are excluded from the
    # DefinedTermSet and listed in their own index section.
    is_q = e.get("kind") == "question"
    url = SITE + "/" + slug + "/"
    ln = e.get("lean") or {}
    mod, thm = ln.get("module"), ln.get("theorem")
    line = thm_line(mod, thm)
    src = None
    if mod:
        src = REPO + "/blob/" + SHA + "/" + mod + (("#L" + str(line)) if line else "")

    hook = " ".join(e["hook"].split())
    layman = " ".join(e["layman"].split())
    # Rendered before the footer is assembled, because linkify is what discovers
    # which external sources this entry actually leans on.
    used, sources = set(), {}
    s_layman = linkify(e["layman"], slug, used, sources)
    s_incsd = linkify(e["in_csd"], slug, used, sources)
    s_math = linkify(e["mathematical"], slug, used, sources)
    s_person = linkify(e["person"], slug, used, sources) if e.get("person") else ""

    if is_q:
        chips = ['<span class="chip"><b>question</b> &middot; answered against '
                 "the machine-checked corpus</span>"]
    else:
        chips = ['<span class="chip"><b>' + E(st.replace("-", " ")) + "</b> &middot; "
                 + E(STATUS_GLOSS.get(st, "")) + "</span>"]
    if thm and src:
        chips.append('<a class="chip" href="' + src + '">Lean <b><code>'
                     + E(thm) + "</code></b></a>")

    rows = []
    if mod:
        rows.append(("Module", ('<a href="' + src + '"><code>' + E(mod) + "</code></a>")
                     if src else ("<code>" + E(mod) + "</code>")))
    for p in e.get("papers") or []:
        rows.append(("Paper", '<a href="https://doi.org/' + p["doi"] + '">'
                     + E(p.get("note", p["doi"])) + "</a>"))
    # The specific onward link into the main site — one page, one sentence saying
    # why a reader of THIS entry would go there. Never a generic call to action;
    # check-glossary.sh validates the URL is on the site_main domain and live.
    sl = e.get("site_link")
    if sl:
        rows.append(("On the site", '<a href="' + sl["url"] + '">'
                     + E(sl["text"]) + "</a>"))
    for x in e.get("external") or []:
        rows.append(("Background", '<a href="' + x["url"] + '">' + E(x["text"]) + "</a>"))
    rel = ", ".join('<a href="' + SITE + "/" + r + '/">' + E(r.replace("-", " ")) + "</a>"
                    for r in e.get("related") or [])
    if rel:
        rows.append(("Related", rel))
    if sources:
        rows.append(("Referenced", ", ".join(
            '<a href="' + u + '">' + E(s) + "</a>"
            for s, u in sorted(sources.items()))))

    body = (
        '<nav class="crumb"><a href="' + SITE_MAIN + '/">Constraint-Surface Dynamics</a>'
        + '<span class="sep">&rsaquo;</span>'
        + '<a href="' + SITE + '/">Glossary</a></nav>'
        + "<h1>" + E(term) + "</h1>"
        + '<p class="hook">' + E(hook) + "</p>"
        + '<div class="strip">' + "".join(chips) + "</div>"
        + '<section class="r1"><h2>' + ("The short answer" if is_q else "In plain terms")
        + "</h2><p>" + s_layman + "</p></section>"
        + '<section class="r2"><h2>' + ("The longer answer" if is_q else "In CSD")
        + "</h2><p>" + s_incsd + "</p></section>"
        + '<section class="r3"><h2>' + ("What is actually proved" if is_q else "Mathematically")
        + "</h2><p>" + s_math + "</p></section>"
        # Optional fourth register: who the name belongs to. A reader meeting an
        # eponym often wants the person, not only the concept, and an entry titled
        # after someone that never says who they were is a small failure of the
        # form. Rendered last because it is context, not content.
        + ('<section class="r4"><h2>The name</h2><p>' + s_person + "</p></section>"
           if s_person else "")
        + '<div class="foot"><dl>'
        + "".join("<dt>" + k + "</dt><dd>" + v + "</dd>" for k, v in rows)
        + "</dl>"
        + '<p class="note">Source links are pinned to a commit, so they do not drift. '
        + "The anchors above are checked mechanically against the Lean tree on every "
        + "build. The mathematics is not, and cannot be: that is a human "
        + "responsibility and it rests with the author.</p>"
        + SITE_LINE + "</div>"
    )

    if is_q:
        jl = {
            "@context": "https://schema.org",
            "@type": "FAQPage",
            "url": url,
            "mainEntity": [{
                "@type": "Question",
                "name": term,
                "acceptedAnswer": {"@type": "Answer", "text": hook + " " + layman},
            }],
        }
    else:
        jl = {
            "@context": "https://schema.org",
            "@type": "DefinedTerm",
            "name": term,
            "description": hook + " " + layman,
            "url": url,
            "inDefinedTermSet": {
                "@type": "DefinedTermSet",
                "name": "Constraint-Surface Dynamics Glossary",
                "url": SITE + "/",
            },
        }
        if e.get("papers"):
            jl["sameAs"] = ["https://doi.org/" + p["doi"] for p in e["papers"]]

    os.makedirs(os.path.join(OUT, slug), exist_ok=True)
    open(os.path.join(OUT, slug, "index.html"), "w", encoding="utf-8").write(
        page(term + " - CSD Glossary", hook, body,
             json.dumps(jl, ensure_ascii=False), url))

    item = ('<li><a href="' + url + '"><span class="t">' + E(term)
            + '</span><span class="h">' + E(hook) + "</span></a></li>")
    (q_items if is_q else idx_items).append(item)
    sitemap.append(url)
    llms.append("- [" + term + "](" + url + "): " + hook)
    md.append("| [" + term + "](" + url + ") | `" + (thm or "") + "` | "
              + ("question" if is_q else st) + " |")

setld = {
    "@context": "https://schema.org",
    "@type": "DefinedTermSet",
    "name": "Constraint-Surface Dynamics Glossary",
    "url": SITE + "/",
    "hasDefinedTerm": [
        {"@type": "DefinedTerm", "name": e["term"], "url": SITE + "/" + e["slug"] + "/"}
        for e in entries if e.get("kind") != "question"
    ],
}
open(os.path.join(OUT, "index.html"), "w", encoding="utf-8").write(page(
    "CSD Glossary",
    "The vocabulary of Constraint-Surface Dynamics, each term explained plainly, "
    "in its role in the programme, and formally, with a machine-checked theorem behind it.",
    '<nav class="crumb"><a href="' + SITE_MAIN + '/">Constraint-Surface Dynamics</a></nav>'
    + "<h1>Glossary</h1>"
    + '<p class="hook">The vocabulary of Constraint-Surface Dynamics. Every term three '
    + "ways: plainly, in the role it plays here, and formally. Each one has a "
    + "machine-checked theorem behind it.</p>"
    # One orienting sentence: what CSD is and where it lives. A reader who lands
    # here from a search result should not have to guess what programme owns the
    # vocabulary. Not a nav bar, not a pitch — one line, two links.
    + '<p class="orient">Constraint-Surface Dynamics is a research programme '
    + "reconstructing quantum mechanics from a single deterministic arena &mdash; start at "
    + '<a href="' + SITE_MAIN + '/">the main site</a> or go straight to '
    + '<a href="' + SITE_MAIN + '/papers">the papers</a>.</p>'
    + '<ul class="idx">' + "".join(idx_items) + "</ul>"
    # Question pages get their own index section: they answer what a sceptical
    # reader types, and burying "Does CSD violate Bell's theorem?" between
    # alphabetical term entries serves nobody. A section heading, not a nav bar.
    + (("<h2 style=\"margin-top:3rem\">Questions</h2>"
        '<ul class="idx">' + "".join(q_items) + "</ul>") if q_items else "")
    + '<div class="foot"><p class="note">Generated from a single source file in '
    + '<a href="' + REPO + '">csd-lean4</a>. Every anchor is verified against the Lean '
    + "tree on each build, and the source links are pinned to a commit.</p>"
    + SITE_LINE + "</div>",
    json.dumps(setld, ensure_ascii=False), SITE + "/"))

open(os.path.join(OUT, "sitemap.xml"), "w", encoding="utf-8").write(
    '<?xml version="1.0" encoding="UTF-8"?>\n'
    '<urlset xmlns="http://www.sitemaps.org/schemas/sitemap/0.9">\n'
    + "".join("  <url><loc>" + u + "</loc></url>\n" for u in sitemap)
    + "</urlset>\n")

open(os.path.join(OUT, "llms.txt"), "w", encoding="utf-8").write(
    "# CSD Glossary\n\n"
    "> The vocabulary of Constraint-Surface Dynamics. Each term is explained in\n"
    "> plain language, in its role within the programme, and formally, and each is\n"
    "> anchored to a machine-checked Lean theorem in csd-lean4.\n\n"
    "## Terms\n\n" + "\n".join(llms) + "\n")

open(os.path.join(OUT, "CNAME"), "w", encoding="utf-8").write(
    SITE.split("//")[1] + "\n")

open("GLOSSARY.md", "w", encoding="utf-8").write(
    "# Glossary\n\n"
    "**Generated by `scripts/gen-glossary.sh` from `docs/glossary.yaml`. "
    "Do not edit by hand.**\n\n"
    "Full entries, with plain-language, CSD-role and formal statements, are published\n"
    "at <" + SITE + "/>.\n\n"
    "This file is the index only. The repo carries navigation, the site carries the\n"
    "prose, and `docs/glossary.yaml` is the single source of both. Header links in the\n"
    "Lean tree are kept symmetric with this index by `scripts/check-glossary.sh`.\n\n"
    "| Term | Lean anchor | Status |\n|---|---|---|\n" + "\n".join(md) + "\n")

print("generated " + str(len(entries)) + " entry page(s) + index, sitemap, llms.txt, "
      "CNAME -> " + OUT + "/")
print("wrote GLOSSARY.md (committed index layer)")
