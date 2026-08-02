#!/usr/bin/env node
// Deterministic static SVG treemap generator for LerayHopf/ Lean source code LOC.
//
// Usage:
//   node generate-code-loc-treemap.mjs <cloc-by-file-json> <output.svg> [output.json]
//
// Input is the output of `cloc --by-file --json --quiet LerayHopf.lean LerayHopf`
// run from the repository root (see tools/code-treemap/package.json "measure" script).
//
// No Date.now()/Math.random()/git-HEAD is used anywhere below: layout, color,
// label, and the embedded "sourceDigest" are a pure function of the measured
// per-file {path, code, comment, blank} data, so the same Lean source tree
// always produces a byte-identical SVG — independent of which commit you
// happen to have checked out when you run this. (An earlier version embedded
// `git rev-parse HEAD` instead; that is circular for a *committed* generated
// artifact — committing the SVG advances HEAD past whatever was embedded in
// it, so the artifact could never reproduce itself byte-for-byte at its own
// commit. See PR #193 review discussion.)

import { readFileSync, writeFileSync, mkdirSync } from "node:fs";
import { dirname } from "node:path";
import { createHash } from "node:crypto";
import { hierarchy, treemap, treemapSquarify } from "d3-hierarchy";

const [, , inputPath, outputSvgPath, outputJsonPathArg] = process.argv;

if (!inputPath || !outputSvgPath) {
  console.error("Usage: node generate-code-loc-treemap.mjs <cloc-by-file-json> <output.svg> [output.json]");
  process.exit(1);
}

if (!outputSvgPath.endsWith(".svg")) {
  console.error(`<output.svg> must end in ".svg" (got "${outputSvgPath}") — refusing to guess a JSON sibling path.`);
  process.exit(1);
}
const outputJsonPath = outputJsonPathArg ?? outputSvgPath.slice(0, -".svg".length) + ".json";
if (outputJsonPath === outputSvgPath) {
  console.error(`Refusing to run: output.json ("${outputJsonPath}") equals output.svg — this would overwrite the SVG.`);
  process.exit(1);
}

// --- 1. Load and validate cloc output -------------------------------------

const raw = JSON.parse(readFileSync(inputPath, "utf8"));
const clocVersion = raw.header?.cloc_version ?? "unknown";

const ROOT_PREFIX = "LerayHopf/";
const ROOT_FILE = "LerayHopf.lean";

/** @type {{path: string, code: number, comment: number, blank: number}[]} */
const files = [];
for (const [path, info] of Object.entries(raw)) {
  if (path === "header" || path === "SUM") continue;
  if (info.language !== "Lean") continue;
  if (path !== ROOT_FILE && !path.startsWith(ROOT_PREFIX)) continue;
  files.push({ path, code: info.code, comment: info.comment, blank: info.blank });
}

// Sort once, up front, so every downstream structure (tree insertion order,
// group-color first-seen order) is a deterministic function of the path
// strings alone, independent of cloc's own JSON key order.
files.sort((a, b) => (a.path < b.path ? -1 : a.path > b.path ? 1 : 0));

if (files.length === 0) {
  console.error(`No Lean files found under ${ROOT_FILE} / ${ROOT_PREFIX} in ${inputPath}`);
  process.exit(1);
}

// --- 2. Group assignment (top-level module -> deterministic color) --------

const KNOWN_GROUP_COLORS = {
  // Okabe–Ito colorblind-safe palette.
  root: "#7f7f7f", // LerayHopf.lean + root-level shared modules directly under LerayHopf/
  Torus: "#56B4E9", // sky blue
  R3: "#D55E00", // vermillion
  Bochner: "#CC79A7", // reddish purple
  Analysis: "#009E73", // bluish green
  Galerkin: "#0072B2", // blue
};
const FALLBACK_PALETTE = ["#E69F00", "#F0E442", "#999999"];

function groupOf(path) {
  if (path === ROOT_FILE) return "root";
  const rest = path.slice(ROOT_PREFIX.length);
  const firstSlash = rest.indexOf("/");
  if (firstSlash === -1) return "root"; // file directly under LerayHopf/
  return rest.slice(0, firstSlash); // top-level directory name, e.g. "R3"
}

const groupOrder = []; // first-seen order, for deterministic fallback-color assignment
for (const f of files) {
  const g = groupOf(f.path);
  if (!groupOrder.includes(g)) groupOrder.push(g);
}
const groupColor = {};
let fallbackIdx = 0;
for (const g of groupOrder) {
  if (KNOWN_GROUP_COLORS[g]) {
    groupColor[g] = KNOWN_GROUP_COLORS[g];
  } else {
    groupColor[g] = FALLBACK_PALETTE[fallbackIdx % FALLBACK_PALETTE.length];
    fallbackIdx += 1;
  }
}

// --- 3. Build the nested tree (root -> top-level dirs/files -> leaf files) -

function makeDir(name) {
  return { name, children: [] };
}

const root = makeDir("LerayHopf");
const dirNodes = new Map(); // top-level dir name -> node

for (const f of files) {
  const group = groupOf(f.path);
  const isRootLevel = f.path === ROOT_FILE || group === "root";
  const leafName = f.path.split("/").pop();
  const leaf = {
    name: leafName,
    path: f.path,
    group,
    value: f.code,
    code: f.code,
    comment: f.comment,
    blank: f.blank,
  };
  if (isRootLevel) {
    root.children.push(leaf);
  } else {
    let dirNode = dirNodes.get(group);
    if (!dirNode) {
      dirNode = makeDir(group);
      dirNode.group = group;
      dirNodes.set(group, dirNode);
      root.children.push(dirNode);
    }
    dirNode.children.push(leaf);
  }
}

// --- 4. Layout --------------------------------------------------------------

const MARGIN = 12;
const TITLE_H = 34;
const LEGEND_H = 26;
const CAPTION_H = 48;
const TREEMAP_W = 1400;
const TREEMAP_H = 760;
const WIDTH = TREEMAP_W + 2 * MARGIN;
const HEIGHT = TITLE_H + TREEMAP_H + LEGEND_H + CAPTION_H + 2 * MARGIN;

const hier = hierarchy(root)
  .sum((d) => d.value ?? 0)
  // Deterministic order: larger files first (nicer squarified packing),
  // ties broken alphabetically by name. Pure function of the data.
  .sort((a, b) => b.value - a.value || (a.data.name < b.data.name ? -1 : a.data.name > b.data.name ? 1 : 0));

const layout = treemap().tile(treemapSquarify).size([TREEMAP_W, TREEMAP_H]).paddingInner(2).paddingOuter(3).round(true);

layout(hier);

// --- 5. Render SVG ------------------------------------------------------

function esc(s) {
  return String(s).replace(/&/g, "&amp;").replace(/</g, "&lt;").replace(/>/g, "&gt;").replace(/"/g, "&quot;");
}

const parts = [];
parts.push(
  `<svg xmlns="http://www.w3.org/2000/svg" viewBox="0 0 ${WIDTH} ${HEIGHT}" font-family="Helvetica, Arial, sans-serif">`
);

// A stable identifier for "which Lean source tree was measured", computed only
// from the measured data itself (not from git state) — so it is reproducible by
// re-running the documented command against the same source tree, regardless of
// which commit happens to be checked out or how many times the artifact has been
// committed/rebased since.
const sourceDigest = createHash("sha256")
  .update(JSON.stringify(files.map((f) => [f.path, f.code, f.comment, f.blank])))
  .digest("hex");

const totalCode = files.reduce((s, f) => s + f.code, 0);
// Summary only in the SVG's <metadata> — the per-file breakdown already lives in
// the companion JSON (outputJsonPath) and each leaf's own <title>; duplicating the
// full file list here would bloat the SVG and noise every regen diff.
const summaryMetadata = {
  generator: "tools/code-treemap/generate-code-loc-treemap.mjs",
  measurementMethod: "cloc --by-file --json --quiet LerayHopf.lean LerayHopf",
  clocVersion,
  sourceDigest: `sha256:${sourceDigest}`,
  fileCount: files.length,
  totalCodeLoc: totalCode,
  // Reflect the actual output path this run was invoked with, not a hard-coded
  // guess — stays correct if the caller passes a custom [output.json].
  perFileDataFile: outputJsonPath,
};
parts.push(`<metadata>${esc(JSON.stringify(summaryMetadata))}</metadata>`);
parts.push(`<title>Lean source code LOC treemap — LerayHopf/</title>`);

// background
parts.push(`<rect x="0" y="0" width="${WIDTH}" height="${HEIGHT}" fill="#ffffff"/>`);

// title bar
parts.push(
  `<text x="${MARGIN}" y="${MARGIN + 22}" font-size="20" font-weight="bold" fill="#111111">Lean source code LOC treemap — LerayHopf/</text>`
);
parts.push(
  `<text x="${WIDTH - MARGIN}" y="${MARGIN + 22}" font-size="12" fill="#555555" text-anchor="end">${esc(
    files.length
  )} files, ${esc(totalCode)} code LOC (cloc ${esc(clocVersion)}, source ${esc(sourceDigest.slice(0, 12))})</text>`
);

const treemapTop = MARGIN + TITLE_H;
parts.push(`<g transform="translate(${MARGIN}, ${treemapTop})">`);

// Internal (directory) nodes at depth 1: unfilled frame + label.
for (const node of hier.descendants()) {
  if (node.depth !== 1 || !node.children) continue;
  const w = node.x1 - node.x0;
  const h = node.y1 - node.y0;
  parts.push(
    `<rect x="${node.x0}" y="${node.y0}" width="${w}" height="${h}" fill="none" stroke="#333333" stroke-width="1.5"/>`
  );
  if (w > 60 && h > 16) {
    parts.push(
      `<text x="${node.x0 + 4}" y="${node.y0 + 13}" font-size="12" font-weight="bold" fill="#222222">${esc(
        node.data.name
      )}/</text>`
    );
  }
}

// Label contrast: pick black or white per tile from the tile's own colour, rather than
// hard-coding white. Several of the palette entries are light enough that white labels fall
// under the WCAG AA 4.5:1 threshold for normal-size text — e.g. Torus `#56B4E9` at 2.31:1 and
// the first fallback colour `#E69F00` at 2.25:1. This is a pure function of the fill colour,
// so the output stays deterministic.
function relativeLuminance(hex) {
  const h = hex.replace("#", "");
  const channels = [0, 2, 4].map((i) => parseInt(h.slice(i, i + 2), 16) / 255);
  const [r, g, b] = channels.map((c) =>
    c <= 0.03928 ? c / 12.92 : Math.pow((c + 0.055) / 1.055, 2.4)
  );
  return 0.2126 * r + 0.7152 * g + 0.0722 * b;
}
function contrastRatio(hexA, hexB) {
  const a = relativeLuminance(hexA);
  const b = relativeLuminance(hexB);
  return (Math.max(a, b) + 0.05) / (Math.min(a, b) + 0.05);
}
function labelColorFor(fill) {
  return contrastRatio(fill, "#000000") >= contrastRatio(fill, "#ffffff")
    ? "#000000"
    : "#ffffff";
}

// Leaf nodes: colored rect + optional label + title (tooltip).
for (const node of hier.leaves()) {
  const d = node.data;
  const w = node.x1 - node.x0;
  const h = node.y1 - node.y0;
  const color = groupColor[d.group] ?? "#cccccc";
  const labelColor = labelColorFor(color);
  parts.push(`<g>`);
  parts.push(
    `<rect x="${node.x0}" y="${node.y0}" width="${w}" height="${h}" fill="${color}" stroke="#ffffff" stroke-width="1"/>`
  );
  parts.push(
    `<title>${esc(d.path)}\ncode: ${esc(d.code)}\ncomment: ${esc(d.comment)}\nblank: ${esc(d.blank)}</title>`
  );
  if (w > 46 && h > 24) {
    const nameFontSize = 10;
    const locFontSize = 10;
    // Fit long file names by clipping via a clip-path keyed on this rect.
    const clipId = `clip-${esc(d.path).replace(/[^a-zA-Z0-9]/g, "-")}`;
    parts.push(
      `<clipPath id="${clipId}"><rect x="${node.x0}" y="${node.y0}" width="${w}" height="${h}"/></clipPath>`
    );
    parts.push(`<g clip-path="url(#${clipId})">`);
    parts.push(
      `<text x="${node.x0 + 3}" y="${node.y0 + 12}" font-size="${nameFontSize}" fill="${labelColor}">${esc(d.name)}</text>`
    );
    parts.push(
      `<text x="${node.x0 + 3}" y="${node.y0 + 24}" font-size="${locFontSize}" fill="${labelColor}">${esc(
        d.code
      )} LOC</text>`
    );
    parts.push(`</g>`);
  }
  parts.push(`</g>`);
}

parts.push(`</g>`); // end treemap group

// legend
const legendY = treemapTop + TREEMAP_H + 20;
let legendX = MARGIN;
for (const g of groupOrder) {
  const label = g === "root" ? "root-level (LerayHopf.lean + shared)" : `${g}/`;
  parts.push(`<rect x="${legendX}" y="${legendY - 10}" width="12" height="12" fill="${groupColor[g]}"/>`);
  parts.push(`<text x="${legendX + 16}" y="${legendY}" font-size="11" fill="#222222">${esc(label)}</text>`);
  legendX += 16 + label.length * 6.2 + 22;
}

// caption / disclaimer, so the SVG is self-explanatory when viewed standalone
const captionY1 = legendY + 22;
const captionY2 = captionY1 + 15;
parts.push(
  `<text x="${MARGIN}" y="${captionY1}" font-size="11.5" fill="#333333">Rectangle area is proportional to code LOC (non-comment, non-blank physical lines) per Lean file, measured with cloc.</text>`
);
parts.push(
  `<text x="${MARGIN}" y="${captionY2}" font-size="11.5" fill="#333333">This figure does not represent proof difficulty, mathematical importance, or code quality.</text>`
);

parts.push(`</svg>\n`);

mkdirSync(dirname(outputSvgPath), { recursive: true });
writeFileSync(outputSvgPath, parts.join("\n"));

const fullMetadata = {
  generator: summaryMetadata.generator,
  measurementMethod: summaryMetadata.measurementMethod,
  clocVersion: summaryMetadata.clocVersion,
  sourceDigest: summaryMetadata.sourceDigest,
  fileCount: summaryMetadata.fileCount,
  totalCodeLoc: summaryMetadata.totalCodeLoc,
  files: files.map((f) => ({ path: f.path, code: f.code, comment: f.comment, blank: f.blank })),
};

mkdirSync(dirname(outputJsonPath), { recursive: true });
writeFileSync(outputJsonPath, JSON.stringify(fullMetadata, null, 2) + "\n");

console.log(`Wrote ${outputSvgPath} and ${outputJsonPath} (${files.length} files, ${totalCode} code LOC).`);
