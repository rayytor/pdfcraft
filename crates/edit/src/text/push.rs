//! Text below moves down (Dokuman): when a rewritten paragraph needs more height than it had,
//! what is drawn under it in its column moves down to make room, so the new lines don't touch or
//! cover it. Paragraphs, pictures (and grouped artwork) and drawn lines and boxes (a table's
//! rules) move; things beside the paragraph's column, above it or reaching up past its bottom stay.
//!
//! Things below are taken in bands from the top down (a band is everything whose heights overlap,
//! so a table with its vertical rules is one band). Each band keeps its distance to the band
//! above it, except that a gap larger than [`GAP_ROWS`] of the paragraph's rows (the empty space
//! above a footer, say) gives up its extra room first: a footer moves only once that is used up.
//! The paragraph growing past the page's bottom edge is not handled: what reaches it is cut off.

use std::collections::{BTreeMap, BTreeSet, HashMap};

use pdfcraft_content::{Matrix, Op};
use pdfcraft_cos::{Document, Object};

use super::{
    BlockKey, BlockStyle, EditError, LineEdit, Read, TextSession, content_streams, joined, page_dict, rewrite_block, rewritten_contents, splice,
    text_blocks, translate_blocks,
};

/// A gap wider than this many of the paragraph's rows gives up its extra room before what lies
/// below it moves.
const GAP_ROWS: f64 = 2.0;
/// Growth smaller than this (points) moves nothing.
const MIN_GROWTH: f64 = 0.1;
/// At most this many drawn paths are looked at on one page.
const MAX_PATHS: usize = 20_000;

/// [`rewrite_block`] with [`BlockStyle::push_below`]: rewrites paragraph `block` and moves what
/// lies under it down by as much as it grew. One edit: on a refusal nothing changes.
pub(crate) fn rewrite_pushing(doc: &mut Document, page: usize, block: usize, text: Option<&str>, style: &BlockStyle) -> Result<LineEdit, EditError> {
    let plain = BlockStyle { push_below: false, ..style.clone() };
    let blocks = text_blocks(doc, page)?;
    let source = blocks.get(block).cloned().ok_or_else(|| EditError::Invalid(format!("page {} has no paragraph {}", page + 1, block + 1)))?;
    let upright = source.rotation.abs() < 0.01;
    let draft = text.unwrap_or(&source.editor_text);
    let grown =
        if upright { TextSession::open(doc, page, block)?.layout(draft, &plain)?.draft_rect.map_or(0.0, |r| source.rect[1] - r[1]) } else { 0.0 };
    if !(grown.is_finite() && grown > MIN_GROWTH) {
        return rewrite_block(doc, page, block, text, &plain);
    }
    let mut work = doc.clone();
    push_below(&mut work, page, &blocks, block, grown)?;
    // Moving paragraphs regroups the page, so the edited one is found again by its text and box.
    let index = BlockKey::of(&source)
        .find(&text_blocks(&work, page)?, block)
        .ok_or_else(|| EditError::Invalid("the paragraph changed while the text below it moved".into()))?;
    let edit = rewrite_block(&mut work, page, index, text, &plain)?;
    *doc = work;
    Ok(edit)
}

#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord)]
enum Thing {
    /// A paragraph, by its index in the page's paragraphs as read before anything moved.
    Paragraph(usize),
    /// A picture or grouped artwork, by its index in [`crate::page_images`].
    Picture(usize),
    /// A drawn path, by its index in [`page_paths`].
    Path(usize),
}

/// Moves what lies under paragraph `block` (of `blocks`, the page's paragraphs) down, making
/// `grown` points of room below it.
fn push_below(doc: &mut Document, page: usize, blocks: &[super::TextBlock], block: usize, grown: f64) -> Result<(), EditError> {
    let source = &blocks[block];
    let [left, bottom, right, top] = source.rect;
    let rows = source.rows.len().max(1) as f64;
    let row = ((top - bottom) / rows).max(1.0);
    // A neighbour's box may reach a little into the paragraph's (descenders, tight leading).
    let under = |r: [f64; 4]| r[3] <= bottom + row * 0.25;

    let mut found: Vec<(Thing, [f64; 4])> = Vec::new();
    for (i, b) in blocks.iter().enumerate() {
        if i != block && under(b.rect) {
            found.push((Thing::Paragraph(i), b.rect));
        }
    }
    let added: BTreeSet<_> = crate::list_added(doc).into_iter().filter(|a| a.page == page).map(|a| a.obj).collect();
    for (i, image) in crate::images::selectable_images(doc, page, &added)? {
        if let Some(r) = image.visible_rect.filter(|r| under(*r)) {
            found.push((Thing::Picture(i), r));
        }
    }
    let paths = page_paths(doc, page)?;
    for (i, p) in paths.iter().enumerate() {
        if under(p.rect) {
            found.push((Thing::Path(i), p.rect));
        }
    }
    let mut things = in_column(found, left, right);
    let shifts = band_shifts(&mut things, bottom, grown, row * GAP_ROWS);

    // Drawn paths first: their operator indexes are from the page as it is now.
    let moves: BTreeMap<usize, f64> = shifts.iter().filter_map(|(t, s)| if let Thing::Path(i) = t { Some((*i, *s)) } else { None }).collect();
    translate_paths(doc, page, &paths, &moves)?;
    let mut pictures: BTreeMap<u64, Vec<usize>> = BTreeMap::new();
    let mut paragraphs: BTreeMap<u64, Vec<usize>> = BTreeMap::new();
    for (t, s) in &shifts {
        match t {
            Thing::Picture(i) => pictures.entry(s.to_bits()).or_default().push(*i),
            Thing::Paragraph(i) => paragraphs.entry(s.to_bits()).or_default().push(*i),
            Thing::Path(_) => {}
        }
    }
    for (shift, indexes) in pictures {
        crate::images::translate_images(doc, page, &indexes, [0.0, -f64::from_bits(shift)])?;
    }
    // Paragraphs that moved regroup the page, so each group is found again by text and box.
    for (shift, indexes) in paragraphs {
        let now = text_blocks(doc, page)?;
        let found = indexes
            .iter()
            .map(|i| {
                BlockKey::of(&blocks[*i]).find(&now, *i).ok_or_else(|| EditError::Invalid("a paragraph below the edit could not be moved".into()))
            })
            .collect::<Result<Vec<_>, _>>()?;
        translate_blocks(doc, page, &found, [0.0, -f64::from_bits(shift)])?;
    }
    Ok(())
}

/// Of `found` (things under the paragraph), those in its column: under its width, and what
/// touches those at the same height, however far that reaches (a table's border and the rest of a
/// row the paragraph is narrower than). Things beside the column that touch nothing in it stay.
fn in_column(found: Vec<(Thing, [f64; 4])>, left: f64, right: f64) -> Vec<(Thing, [f64; 4])> {
    // Boxes this close (points) touch: a table's rules meet edge to edge.
    const TOUCH: f64 = 1.0;
    let touch = |a: [f64; 4], b: [f64; 4]| a[0] <= b[2] + TOUCH && b[0] <= a[2] + TOUCH && a[1] <= b[3] + TOUCH && b[1] <= a[3] + TOUCH;
    let mut taken: Vec<bool> = found.iter().map(|(_, r)| r[0] < right && r[2] > left).collect();
    let mut queue: Vec<usize> = (0..found.len()).filter(|i| taken[*i]).collect();
    while let Some(i) = queue.pop() {
        for j in 0..found.len() {
            if !taken[j] && touch(found[i].1, found[j].1) {
                taken[j] = true;
                queue.push(j);
            }
        }
    }
    found.into_iter().zip(taken).filter_map(|(t, keep)| keep.then_some(t)).collect()
}

/// How far down each of `things` moves (points, positive) when what lies above them, ending at
/// `bottom`, grows `grown` points lower. Bands are taken top down; a gap wider than `max_gap`
/// shrinks to it before the band below it moves. Things that don't move are left out.
fn band_shifts(things: &mut [(Thing, [f64; 4])], bottom: f64, grown: f64, max_gap: f64) -> Vec<(Thing, f64)> {
    things.sort_by(|a, b| b.1[3].total_cmp(&a.1[3]));
    let mut out = Vec::new();
    let (mut above, mut shift) = (bottom, grown);
    let mut i = 0;
    while i < things.len() && shift > MIN_GROWTH {
        // One band: everything whose height overlaps the band's so far.
        let (band_top, mut band_bottom) = (things[i].1[3], things[i].1[1]);
        let mut j = i + 1;
        while j < things.len() && things[j].1[3] > band_bottom {
            band_bottom = band_bottom.min(things[j].1[1]);
            j += 1;
        }
        let gap = above - band_top;
        if gap > max_gap {
            shift = (shift - (gap - max_gap)).max(0.0);
        }
        if shift > MIN_GROWTH {
            out.extend(things[i..j].iter().map(|(t, _)| (*t, shift)));
        }
        above = band_bottom;
        i = j;
    }
    out
}

/// A drawn path: the operators that build it, and its box in user space.
struct PagePath {
    ops: Vec<usize>,
    rect: [f64; 4],
}

/// The paths a page's own content draws or clips with (not those inside forms), each with the
/// operators that build it, as indexes among the page's streams parsed joined.
fn page_paths(doc: &Document, page: usize) -> Result<Vec<PagePath>, EditError> {
    let p = page_dict(doc, page)?;
    let streams = content_streams(doc, &p.dict)?;
    if streams.iter().any(|s| s.read != Read::Whole) {
        return Err(EditError::Invalid("the page's content could not be completely read, so the text below the edit can't be moved".into()));
    }
    let ops = joined(&streams).parse().ops;
    let mut out = Vec::new();
    let mut ctm = Matrix::IDENTITY;
    let mut saved = Vec::new();
    let mut building: Vec<usize> = Vec::new();
    let mut rect = [f64::INFINITY, f64::INFINITY, f64::NEG_INFINITY, f64::NEG_INFINITY];
    let add = |rect: &mut [f64; 4], (x, y): (f64, f64)| {
        *rect = [rect[0].min(x), rect[1].min(y), rect[2].max(x), rect[3].max(y)];
    };
    for (index, op) in ops.iter().enumerate() {
        match op.op.as_slice() {
            b"q" => saved.push(ctm),
            b"Q" => ctm = saved.pop().unwrap_or(ctm),
            b"cm" => {
                if let Some(m) = Matrix::from_operands(&op.operands) {
                    ctm = m.then(&ctm);
                }
            }
            b"m" | b"l" | b"c" | b"v" | b"y" | b"re" | b"h" => {
                let nums: Vec<f64> = op.operands.iter().filter_map(Object::as_f64).collect();
                if op.is("re") && nums.len() == 4 {
                    let [x, y, w, h] = [nums[0], nums[1], nums[2], nums[3]];
                    for (px, py) in [(x, y), (x + w, y), (x + w, y + h), (x, y + h)] {
                        add(&mut rect, ctm.apply(px, py));
                    }
                } else {
                    for [x, y] in nums.as_chunks::<2>().0 {
                        add(&mut rect, ctm.apply(*x, *y));
                    }
                }
                building.push(index);
            }
            b"W" | b"W*" => {}
            b"S" | b"s" | b"f" | b"F" | b"f*" | b"B" | b"B*" | b"b" | b"b*" | b"n" => {
                if !building.is_empty() && rect.iter().all(|v| v.is_finite()) && out.len() < MAX_PATHS {
                    out.push(PagePath { ops: std::mem::take(&mut building), rect });
                }
                building.clear();
                rect = [f64::INFINITY, f64::INFINITY, f64::NEG_INFINITY, f64::NEG_INFINITY];
            }
            _ => {}
        }
    }
    Ok(out)
}

/// Moves paths `moves` (index into `paths` → points down) by rewriting their coordinates, in the
/// space each was drawn in, so a stroke's width and a clip stay as they were.
fn translate_paths(doc: &mut Document, page: usize, paths: &[PagePath], moves: &BTreeMap<usize, f64>) -> Result<(), EditError> {
    if moves.is_empty() {
        return Ok(());
    }
    let p = page_dict(doc, page)?;
    let streams = content_streams(doc, &p.dict)?;
    let pieces = joined(&streams);
    let ops = pieces.parse().ops;
    // The current transformation at each operator, to turn a move down the page into its own space.
    let mut ctms = Vec::with_capacity(ops.len());
    let (mut ctm, mut saved) = (Matrix::IDENTITY, Vec::new());
    for op in &ops {
        ctms.push(ctm);
        match op.op.as_slice() {
            b"q" => saved.push(ctm),
            b"Q" => ctm = saved.pop().unwrap_or(ctm),
            b"cm" => {
                if let Some(m) = Matrix::from_operands(&op.operands) {
                    ctm = m.then(&ctm);
                }
            }
            _ => {}
        }
    }
    let mut patches: HashMap<usize, Vec<Op>> = HashMap::new();
    for (path, down) in moves {
        let path = paths.get(*path).ok_or_else(|| EditError::Invalid("a drawn line below the edit no longer exists".into()))?;
        for index in &path.ops {
            let op = ops.get(*index).ok_or_else(|| EditError::Invalid("a drawn line below the edit no longer exists".into()))?;
            let inverse = ctms[*index].invert().ok_or_else(|| EditError::Invalid("a drawn line below the edit has no area".into()))?;
            // Only the vertical part of the inverse matters: the move is straight down.
            let [_, _, c, d, _, _] = inverse.0;
            let (dx, dy) = (c * -down, d * -down);
            let name = std::str::from_utf8(&op.op).map_err(|_| EditError::Invalid("a drawn line has an unreadable operator".into()))?;
            let mut nums: Vec<f64> = Vec::new();
            for o in &op.operands {
                nums.push(o.as_f64().ok_or_else(|| EditError::Invalid("a drawn line has an unreadable coordinate".into()))?);
            }
            let moved: Vec<f64> = if op.is("re") {
                nums.iter()
                    .enumerate()
                    .map(|(k, v)| match k {
                        0 => v + dx,
                        1 => v + dy,
                        _ => *v,
                    })
                    .collect()
            } else {
                nums.iter().enumerate().map(|(k, v)| if k % 2 == 0 { v + dx } else { v + dy }).collect()
            };
            if !moved.iter().all(|v| v.is_finite()) {
                return Err(EditError::Invalid("the move of a drawn line is too large".into()));
            }
            patches.insert(*index, vec![Op::new(name, moved.into_iter().map(Object::Real).collect())]);
        }
    }
    let data = splice(&pieces, &ops, |i| patches.remove(&i).map_or((Vec::new(), true), |v| (v, false)));
    let contents = rewritten_contents(doc, &streams, data)?;
    doc.update_dict(p.obj, |d| d.set(b"Contents".to_vec(), contents))?;
    Ok(())
}
