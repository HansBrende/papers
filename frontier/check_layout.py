"""Check the geometry of the frontier map against its drawing rules.

Usage, from any directory:

    uv run --no-project --with shapely python frontier/check_layout.py [path/to/index.html]

Without an argument it reads the index.html next to this script. It rebuilds every drawn piece of the SVG as
a polygon and checks with exact polygon operations that

  * the dark-outlined pieces (one work tape, oblivious data movement, few macroscopic crossings, one
    long-range work head, few large families and the half-bound piece) overlap exactly the pieces listed
    in BANDS, each overlap
    containing a disc of diameter at least MIN_WIDTH, and stay at least GAP_MIN units from all others;
  * every certified cell listed in CELLS is drawn: the region inside its pieces and outside the others
    contains a disc of diameter at least MIN_WIDTH;
  * every inclusion listed in INSIDE holds;
  * no drawn shape lies inside another unless the inclusion is listed in ALLOWED (drawing a shape inside
    another is a claim of inclusion);
  * every dotted ? link joins the outlines of the two shapes listed in UNKNOWN, those shapes are apart, and
    the link crosses no other piece;
  * the strips outside the transposers miss the transposer rectangle, and the green question marks sit in
    the pieces their cards describe.

The reasons for each entry (witness machines and published results) are in frontier-rigour-decisions.md.
The exit status is 1 if any check fails.
"""
import re
import sys
from pathlib import Path

from shapely import affinity
from shapely.geometry import LineString, Point, box
from shapely.ops import polylabel


def width(region):
    """Diameter of the largest disc inside the region (pole of inaccessibility, per component)."""
    parts = getattr(region, "geoms", [region])
    best = 0.0
    for p in parts:
        if p.geom_type == "Polygon" and p.area > 0:
            best = max(best, 2 * polylabel(p, tolerance=0.25).distance(p.exterior))
    return best

AREA_MIN = 120.0  # a drawn overlap must have at least this area to be visible
MIN_WIDTH = 12.0  # ... and contain a disc of at least this diameter
GAP_MIN = 6.0     # shapes drawn apart must be at least this far apart
ON_LINE = 1.5     # a link end must lie within this distance of the outline it joins

# data-id in the SVG -> name used below
PIECES = {"high": "T", "leOpen": "LE", "ob": "O", "obS": "CD", "lowad": "BE", "pc": "PC", "geom": "GEOM",
          "crossings": "CROSS", "onehead": "ONEHEAD", "onetape": "ONETAPE", "movement": "MOVE", "merge": "MERGE",
          "linear": "LINEAR", "passes": "PASSES", "phases": "PHASES"}

# regions derived from the circles: shallow and deep oblivious pieces, low adaptivity without obliviousness,
# high adaptivity
DERIVED = {"S": lambda R: R["CD"].intersection(R["O"]), "D": lambda R: R["O"].difference(R["CD"]),
           "LAO": lambda R: R["LE"].difference(R["O"]), "HA": lambda R: R["T"].difference(R["LE"])}

# the pieces each dark-outlined piece is proved to share a transposer with; it must stay apart from every
# other piece (pairwise claims only: no combination of three or more pieces is claimed)
BANDS = {
    "ONETAPE": {"S", "LAO", "HA", "PC", "GEOM", "CROSS", "ONEHEAD", "MOVE", "MERGE", "LINEAR"},
    "MOVE": {"S", "D", "BE", "PC", "GEOM", "CROSS", "ONEHEAD", "ONETAPE", "MERGE", "LINEAR"},
    "CROSS": {"S", "D", "LAO", "HA", "PC", "GEOM", "MERGE", "LINEAR", "ONETAPE", "MOVE", "ONEHEAD"},
    "ONEHEAD": {"S", "D", "LAO", "HA", "PC", "GEOM", "MERGE", "LINEAR", "ONETAPE", "MOVE", "CROSS"},
    "GEOM": {"S", "BE", "PC", "MERGE", "LINEAR", "ONETAPE", "MOVE", "CROSS", "ONEHEAD"},
    "PC": {"S", "D", "BE", "GEOM", "MERGE", "LINEAR", "ONETAPE", "MOVE", "CROSS", "ONEHEAD"},
}

# certified cells that the drawing shows as regions: (pieces the region lies in, pieces it lies outside).
# The cancelling-copies machine lies in few large families and both overlays, and outside every other red
# piece and the bounded-entry disc.
CELLS = [({"GEOM", "S", "MERGE", "LINEAR"}, {"BE", "PC", "CROSS", "ONEHEAD", "ONETAPE", "MOVE"})]

# pieces a dotted ? link must not cross, apart from the two it joins
LINK_CLEAR = ["BE", "PC", "GEOM", "CROSS", "ONEHEAD", "ONETAPE", "MOVE", "PASSES", "PHASES"]
# pieces the band rule compares against (the low-adaptivity circle, the oblivious circle and the shallow
# circle are covered through S, D, LAO and HA)
COMPARED = ["S", "D", "LAO", "HA", "BE", "PC", "GEOM", "CROSS", "ONEHEAD", "ONETAPE", "MOVE", "MERGE", "LINEAR"]

# required inclusions: (part, whole); "A&B" is an intersection
INSIDE = [("O", "LE"), ("PC", "O"), ("GEOM", "S"), ("MERGE", "O"), ("LINEAR", "O"), ("MOVE", "O"),
          ("MOVE", "MERGE"), ("MOVE", "LINEAR"), ("BE&O", "S"), ("ONETAPE&O", "S")]
INSIDE += [(p, "T") for p in ["LE", "BE", "PC", "GEOM", "CROSS", "ONEHEAD", "ONETAPE", "MOVE", "MERGE", "LINEAR"]]

# drawn inclusions that are proved; any other shape drawn inside another is an error
DRAWN = ["LE", "O", "S", "D", "LAO", "HA", "BE", "PC", "GEOM", "CROSS", "ONEHEAD", "ONETAPE", "MOVE", "MERGE", "LINEAR"]
ALLOWED = {("O", "LE"), ("S", "O"), ("S", "LE"), ("D", "O"), ("D", "LE"), ("LAO", "LE"), ("PC", "O"), ("PC", "LE"),
           ("GEOM", "S"), ("GEOM", "O"), ("GEOM", "LE"), ("MERGE", "O"), ("MERGE", "LE"), ("LINEAR", "O"),
           ("LINEAR", "LE"), ("MOVE", "O"), ("MOVE", "LE"), ("MOVE", "MERGE"), ("MOVE", "LINEAR")}

# pairs joined by a dotted ? link: not known whether they share a transposer
UNKNOWN = {frozenset({"ONETAPE", "BE"}), frozenset({"CROSS", "BE"}), frozenset({"ONEHEAD", "BE"}),
           frozenset({"PHASES", "T"})}

# green question marks: (pieces that must contain the glyph centre, pieces it must keep clear of)
QMARKS = [({"D", "LINEAR"}, {"PC", "MOVE", "CROSS", "ONEHEAD", "MERGE"}),
          ({"HA"}, {"BE", "CROSS", "ONEHEAD", "ONETAPE"})]


def attrs(text):
    return dict(re.findall(r'([\w-]+)="([^"]*)"', text))


def shape(kind, a):
    if kind == "rect":
        x, y, w, h = (float(a[k]) for k in ("x", "y", "width", "height"))
        return box(x, y, x + w, y + h)
    if kind == "circle":
        return Point(float(a["cx"]), float(a["cy"])).buffer(float(a["r"]), 256)
    cx, cy, rx, ry = (float(a[k]) for k in ("cx", "cy", "rx", "ry"))
    e = affinity.scale(Point(0, 0).buffer(1, 256), rx, ry)
    m = re.search(r"rotate\(([-\d.]+)(?: ([-\d.]+) ([-\d.]+))?\)", a.get("transform", ""))
    if m:
        if m.group(2) is not None and (float(m.group(2)) != cx or float(m.group(3)) != cy):
            raise ValueError("an ellipse must rotate about its own centre")
        e = affinity.rotate(e, float(m.group(1)), origin=(0, 0))
    return affinity.translate(e, cx, cy)


def main():
    path = Path(sys.argv[1]) if len(sys.argv) > 1 else Path(__file__).with_name("index.html")
    html = path.read_text(encoding="utf-8")
    R = {}
    for m in re.finditer(r'<g class="r" tabindex="0" data-id="(\w+)"[^>]*>\s*<(circle|ellipse|rect) ([^>]*)>', html):
        if m.group(1) in PIECES:
            R[PIECES[m.group(1)]] = shape(m.group(2), attrs(m.group(3)))
    frame = re.search(r'<rect ([^>]*class="frame"[^>]*)>', html)
    R["FRAME"] = shape("rect", attrs(frame.group(1)))
    missing = set(PIECES.values()) - set(R)
    if missing:
        sys.exit(f"pieces not found in the SVG: {sorted(missing)}")
    for name, make in DERIVED.items():
        R[name] = make(R)

    def get(name):
        if "&" in name:
            a, b = name.split("&")
            return R[a].intersection(R[b])
        return R[name]

    problems = []
    for band, shared in BANDS.items():
        for other in COMPARED:
            if other == band:
                continue
            if other in shared:
                both = R[band].intersection(R[other])
                if both.area < AREA_MIN:
                    problems.append(f"{band} must overlap {other} (area {both.area:.0f})")
                elif width(both) < MIN_WIDTH:
                    problems.append(f"{band} overlaps {other} too thinly (width {width(both):.1f})")
            else:
                gap = R[band].distance(R[other])
                if gap < GAP_MIN:
                    problems.append(f"{band} must stay apart from {other} (gap {gap:.1f})")
    for ins, outs in CELLS:
        region = R["T"]
        for n in ins:
            region = region.intersection(R[n])
        for n in outs:
            region = region.difference(R[n])
        if width(region) < MIN_WIDTH:
            problems.append(f"cell inside {sorted(ins)} and outside {sorted(outs)} is not drawn "
                            f"(width {width(region):.1f})")
    for part, whole in INSIDE:
        outside = get(part).difference(get(whole)).area
        if outside > 1.0:
            problems.append(f"{part} must lie inside {whole} ({outside:.0f} outside)")
    for a in DRAWN:
        for b in DRAWN:
            if a != b and (a, b) not in ALLOWED and R[a].difference(R[b]).area < 1.0:
                problems.append(f"{a} is drawn inside {b}, an inclusion that is not proved")
    for strip in ("PASSES", "PHASES"):
        if R[strip].intersection(R["T"]).area > 0 or R[strip].difference(R["FRAME"]).area > 1.0:
            problems.append(f"{strip} must lie in the frame, outside the transposers")
    if R["T"].difference(R["FRAME"]).area > 1.0:
        problems.append("the transposers must lie inside the frame")

    links = re.findall(r'<g class="unk"[^>]*>\s*<line ([^>]*)>', html)
    joined = []
    for text in links:
        a = attrs(text)
        ends = [Point(float(a["x1"]), float(a["y1"])), Point(float(a["x2"]), float(a["y2"]))]
        names = []
        for p in ends:
            near = [n for n in ["T", "BE", "PC", "GEOM", "CROSS", "ONEHEAD", "ONETAPE", "MOVE", "PASSES", "PHASES"]
                    if R[n].exterior.distance(p) <= ON_LINE]
            names.append(near)
        pair = next((frozenset({x, y}) for x in names[0] for y in names[1] if frozenset({x, y}) in UNKNOWN), None)
        if pair is None:
            problems.append(f"a dotted ? link joins {names[0]} to {names[1]}, not a listed unknown pair")
        else:
            joined.append(pair)
            x, y = sorted(pair)
            if R[x].distance(R[y]) < GAP_MIN:
                problems.append(f"{x} and {y} are joined by a ? link but drawn touching")
            if LineString(ends).length < 2 * GAP_MIN:
                problems.append(f"the ? link between {x} and {y} is too short to see")
            seg = LineString(ends)
            inner = LineString([seg.interpolate(3), seg.interpolate(seg.length - 3)])
            for n in LINK_CLEAR:
                if n not in pair and inner.intersects(R[n].buffer(-0.5)):
                    problems.append(f"the ? link between {x} and {y} crosses {n}")
    for pair in UNKNOWN - set(joined):
        problems.append(f"no dotted ? link joins {sorted(pair)}")

    marks = re.findall(r'<text x="([\d.]+)" y="([\d.]+)" class="qmark[^"]*" font-size="34"', html)
    if len(marks) != len(QMARKS):
        problems.append(f"expected {len(QMARKS)} green question marks, found {len(marks)}")
    for (x, y), (ins, clear) in zip(marks, QMARKS):
        centre = Point(float(x) + 9, float(y) - 12)  # glyph centre at font size 34
        for n in ins:
            if not R[n].buffer(-12).contains(centre):
                problems.append(f"question mark at ({x}, {y}) is not well inside {n}")
        for n in clear:
            if R[n].distance(centre) < 16:
                problems.append(f"question mark at ({x}, {y}) is too close to {n}")

    for band in BANDS:
        met = [o for o in COMPARED if o != band and R[band].intersection(R[o]).area >= AREA_MIN]
        print(f"{band} overlaps: {', '.join(met)}")
    for line in problems:
        print("FAIL", line)
    print("layout check passed" if not problems else f"layout check failed: {len(problems)} problems")
    sys.exit(1 if problems else 0)


main()
