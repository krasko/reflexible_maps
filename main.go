package main

import (
	"flag"
	"fmt"
	"io/ioutil"
	"os"
	"path"
	"sort"
	"strconv"
	"strings"
	"time"
)

// degs is a slice of vertex degrees
type degs []int

// copy copies the slice, so that the copy can be modified safely without
// affecting the initial slice.
func (d degs) copy() degs {
	r := make(degs, len(d))
	copy(r, d)
	return r
}

// sum counts the sum of vertex degrees.
func (d degs) sum() (s int) {
	for _, d := range d {
		s += d
	}
	return s
}

// bVer denotes a boundary vertex by the presence of boundary darts incident to it.
type bVer struct{ l, r bool }

// hole defines a boundary component of a surface.
// If the root lies not on this boundary component, this slice is considered up to cyclic shifts.
type hole []bVer

// copy deep-copies this hole.
func (h hole) copy() hole {
	r := make(hole, len(h))
	copy(r, h)
	return r
}

// insert inserts a new bVer into this hole into every position, with every combination
// of boundary vertices; hole is rotated so that the inserted vertex is always at index 0
// in the result.
func (h hole) insert() (res holes) {
	for mask := 0; mask < 4; mask++ {
		n := hole{{mask&1 > 0, mask&2 > 0}}
		rot := h.rotate()
		if len(rot) == 0 {
			rot = holes{{}}
		}
		for _, h := range rot {
			res = append(res, append(n, h...))
		}
	}
	return res
}

// split splits this hole into two holes, along an edge from vertex 0 to every
// other bVer and to any interval between two bVers.
func (h hole) split() (res [][2]hole) {
	for i := 1; i < len(h); i++ {
		res = append(res, [2]hole{
			append(hole{{h[i].l, h[0].r}}, h[i+1:]...),
			append(hole{{h[0].l, h[i].r}}, h[1:i]...),
		})
	}
	for i := 1; i <= len(h); i++ {
		for mask := 0; mask < 4; mask++ {
			res = append(res, [2]hole{
				append(hole{{mask&1 > 0, h[0].r}}, h[i:]...),
				append(hole{{h[0].l, mask&2 > 0}}, h[1:i]...),
			})
		}
	}
	return res
}

// flip returns the result of fliping this hole, that is,
// changing the cyclic ordering of vertices to opposite.
func (h hole) flip() hole {
	res := make(hole, len(h))
	for i := range h {
		res[i] = h[(len(h)-i)%len(h)]
		res[i].l, res[i].r = res[i].r, res[i].l
	}
	return res
}

// rotate returns the result of cyclically permuting this hole for every possible index.
func (h hole) rotate() (res holes) {
	for i := range h {
		var n hole
		n = append(n, h[i:]...)
		n = append(n, h[:i]...)
		res = append(res, n)
	}
	return res
}

// normalize replaces this hole with its canonical representation,
// which is equal to some cyclic shift of it. All holes that
// differ only by cyclic shifts will have the same canonical representation.
// This function uses Booth's Algorithm for finding lexicographically minimal string rotation.
func (h hole) normalize() {
	s := make([]int, len(h))
	for i, b := range h {
		if b.l {
			s[i] |= 0x1
		}
		if b.r {
			s[i] |= 0x2
		}
	}
	s = append(s, s...)
	f := make([]int, len(s))
	for i := range s {
		f[i] = -1
	}
	k := 0
	for j := 1; j < len(s); j++ {
		sj := s[j]
		i := f[j-k-1]
		for i != -1 && sj != s[k+i+1] {
			if sj < s[k+i+1] {
				k = j - i - 1
			}
			i = f[i]
		}
		if sj != s[k+i+1] {
			if sj < s[k] {
				k = j
			}
			f[j-k] = -1
		} else {
			f[j-k] = i + 1
		}
	}
	if k == 0 {
		return
	}
	n := append(h[k:], h[:k]...)
	copy(h, n)
}

// holes is a slice of hole-s.
type holes []hole

// Len is a utility function required for sorting holes.
func (h holes) Len() int {
	return len(h)
}

// Swap is a utility function required for sorting holes.
func (h holes) Swap(i, j int) {
	h[i], h[j] = h[j], h[i]
}

// Less is a utility function required for sorting holes.
func (h holes) Less(i, j int) bool {
	if len(h[i]) != len(h[j]) {
		return len(h[i]) < len(h[j])
	}
	for k := range h[i] {
		if h[i][k].l != h[j][k].l {
			return h[i][k].l
		}
		if h[i][k].r != h[j][k].r {
			return h[i][k].r
		}
	}
	return false
}

// normalize normalizes this slice of holes:
// normalizes every hole individually and then sorts the result.
func (hs holes) normalize() {
	for _, h := range hs {
		h.normalize()
	}
	sort.Sort(hs)
}

// copy deep-copies a slice of holes.
func (hs holes) copy() holes {
	r := make(holes, len(hs))
	for i, h := range hs {
		r[i] = h.copy()
	}
	return r
}

// filp flips all holes in the slice.
func (hs holes) flip() (res holes) {
	for _, h := range hs {
		res = append(res, h.flip())
	}
	return res
}

// selAll returns the result of "selecting" each hole in this slice, that is, moving
// it to the 0th position.
func (hs holes) selAll() (res []holes) {
	for i, h := range hs {
		nhs := make(holes, len(hs))
		nhs[0] = h
		copy(nhs[1:], hs[:i])
		copy(nhs[i+1:], hs[i+1:])
		res = append(res, nhs)
	}
	return res
}

// split is an utility data structure that denotes which of two disjoint subsets
// i-th element of some set belongs to.
type split struct{ i, part int }

// powerSet returns all ways of splitting a given n-element set into two disjoint subsets.
func powerSet(n int) (res [][]split) {
	res = make([][]split, 1<<uint8(n))
	for i := 0; i < (1 << uint8(n)); i++ {
		splits := make([]split, n)
		for j := 0; j < n; j++ {
			if (1<<uint8(j))&i != 0 {
				splits[j] = split{j, 0}
			} else {
				splits[j] = split{j, 1}
			}
		}
		res[i] = splits
	}
	return res
}

// IRRELEVANT is a special value denoting that we should ignore the value of innervf
// and count all maps regardless of the number of inner vertices and faces.
const IRRELEVANT = 128

// signature is the core object of the computation this program performs:
// it defines a class of maps on a surface that can be counted recursively.
type signature struct {
	// If !maybeNonorientable, the number of handles.
	// If maybeNonorientable, this number is defined by the Euler's characteristics in such a way
	// that if the map is indeed non-orientable, this is the number of crosscaps.
	genus int
	// Boundary components of the surface that the root vertex does not lie on.
	holes holes
	// Degrees of non-root distinguished vertices lying in the surface interior.
	degs degs
	// Total darts on the surface (strictly speaking, 2 * #flags).
	darts int
	// If nil or empty, the root vertex is internal;
	// otherwise it's the boundary component containing the root vertex.
	hole0 hole
	// Degree of the root vertex.
	deg0 int
	// If false, the surface is orientable;
	// if true, we count maps regardless of surface orientability.
	maybeNonorientable bool
	// The sum of numbers of vertices and faces in the interior of the surface.
	innervf int
}

// copy deep-copies this signature.
func (s signature) copy() *signature {
	ns := s
	ns.degs = s.degs.copy()
	ns.holes = s.holes.copy()
	return &ns
}

// incInnerVF increases the value of innervf respecting special value "IRRELEVANT".
func (s *signature) incInnerVF(val int) {
	if s.innervf == IRRELEVANT {
		return
	}
	s.innervf += val
}

// splitInnerVF splits interior vertices and faces among two new maps in all possible ways.
func (s *signature) splitInnerVF() (res [][2]int) {
	if s.innervf == IRRELEVANT {
		return [][2]int{{IRRELEVANT, IRRELEVANT}}
	}
	for i := 0; i <= s.innervf; i++ {
		res = append(res, [2]int{i, s.innervf - i})
	}
	return res
}

// isClosedSurface returns true iff the surface has no boundary.
func (s *signature) isClosedSurface() bool {
	return len(s.hole0) == 0 && len(s.holes) == 0
}

// split split this signature into two, in all possible ways:
// chosen vertices and holes are split among two maps in 2^n ways,
// genus and darts are split as "unlabelled" objects, in n+1 ways.
func (s *signature) split() (res [][2]signature) {
	degSet := powerSet(len(s.degs))
	holeSet := powerSet(len(s.holes))
	for _, degc := range degSet {
		var degss [2]degs
		for _, d := range degc {
			degss[d.part] = append(degss[d.part], s.degs[d.i])
		}
		lb2 := degss[0].sum()
		hb2 := s.darts - degss[1].sum()
		if lb2 > hb2 {
			continue
		}
		for _, holec := range holeSet {
			holess := [...]holes{
				make(holes, 0, len(holec)),
				make(holes, 0, len(holec)),
			}
			for _, h := range holec {
				holess[h.part] = append(holess[h.part], s.holes[h.i])
			}
			for g := 0; g <= s.genus; g++ {
				lb, hb := 0, s.darts
				/* optimization */
				lb, hb = 2*g+len(holess[0])+2*len(degss[0]), s.darts-2*(s.genus-g)-len(holess[1])-2*len(degss[1])
				if !s.maybeNonorientable {
					lb += 2 * g
					hb -= 2 * (s.genus - g)
				}
				if lb2 > lb {
					lb = lb2
				}
				if hb2 < hb {
					hb = hb2
				}
				/* end optimization */
				for d := lb; d <= hb; d++ {
					for _, ivf := range s.splitInnerVF() {
						res = append(res, [2]signature{{
							genus:              g,
							holes:              holess[0],
							degs:               degss[0],
							darts:              d,
							hole0:              s.hole0,
							deg0:               s.deg0,
							maybeNonorientable: s.maybeNonorientable,
							innervf:            ivf[0],
						}, {
							genus:              s.genus - g,
							holes:              holess[1],
							degs:               degss[1],
							darts:              s.darts - d,
							maybeNonorientable: s.maybeNonorientable,
							innervf:            ivf[1],
						}})
					}
				}
			}
		}
	}
	return res
}

// String returns a string representation of this signature which
// defines it uniquely; it is needed in order to use signatures as map keys.
func (s *signature) String() string {
	// We encode each parameter with 1 byte, assuming it never goes above
	// 255. Realistic values of each parameter are < 30.
	cnt := 1 + len(s.hole0)
	for _, h := range s.holes {
		cnt += 1 + len(h)
	}
	b := make([]byte, 6+cnt+len(s.degs))
	b[0] = byte(s.innervf)
	b[1] = byte(s.darts)
	b[2] = byte(s.genus)
	b[3] = byte(s.deg0)
	if s.maybeNonorientable {
		b[4] = 1
	}
	j := 5
	b[j] = byte(len(s.holes))
	j++
	for i := 0; i <= len(s.holes); i++ {
		h := s.hole0
		if i != len(s.holes) {
			h = s.holes[i]
		}
		b[j] = byte(len(h))
		j++
		for _, v := range h {
			if v.l {
				b[j] |= 2
			}
			if v.r {
				b[j] |= 4
			}
			j++
		}
	}
	for _, d := range s.degs {
		b[j] = byte(d)
		j++
	}
	return string(b)
}

// m is a cache storing a mapping from map signature (as string)
// to the number of maps with this signature.
var m = map[string]int64{
	(&signature{0, nil, nil, 0, nil, 0, true, 2}).String():                1,
	(&signature{0, nil, nil, 0, nil, 0, false, 2}).String():               1,
	(&signature{0, nil, nil, 0, nil, 0, true, IRRELEVANT}).String():       1,
	(&signature{0, nil, nil, 0, nil, 0, false, IRRELEVANT}).String():      1,
	(&signature{0, nil, nil, 0, hole{{}}, 0, true, 0}).String():           1,
	(&signature{0, nil, nil, 0, hole{{}}, 0, false, 0}).String():          1,
	(&signature{0, nil, nil, 0, hole{{}}, 0, true, IRRELEVANT}).String():  1,
	(&signature{0, nil, nil, 0, hole{{}}, 0, false, IRRELEVANT}).String(): 1,
}

// Chi is the Euler characteristic of the surface.
func (s *signature) Chi() int {
	var res int
	if len(s.hole0) > 0 {
		res--
	}
	if s.maybeNonorientable {
		res += 2 - s.genus - len(s.holes)
	} else {
		res += 2 - 2*s.genus - len(s.holes)
	}
	return res
}

// reduce_JoinInternal contracts an edge that leads into a non-distinguished vertex in the surface interior.
func (s signature) reduce_JoinInternal() (res []signature) {
	if s.deg0 <= 0 {
		return nil
	}
	s.darts -= 2
	s.incInnerVF(-1)
	for d := s.deg0 - 1; d <= s.darts-s.degs.sum(); d++ {
		s := s
		s.deg0 = d
		res = append(res, s)
	}
	return res
}

// reduce_JoinInternalChosen contracts an edge that leads into a distinguished vertex in the surface interior.
func (s signature) reduce_JoinInternalChosen() (res []signature) {
	if s.deg0 <= 0 {
		return nil
	}
	s.incInnerVF(-1)
	for i := 0; i < len(s.degs); i++ {
		s := s
		s.deg0 += s.degs[i] - 2
		s.degs = append(append(degs{}, s.degs[:i]...), s.degs[i+1:]...)
		s.darts -= 2
		res = append(res, s)
	}
	if s.maybeNonorientable {
		return append(res, res...)
	}
	return res
}

// zeroCount is a debug counter that counts how many times signature.count()
// returned zero or non-zero by computing the value instead of taking it from cache.
var zeroCount = map[bool]int{}

// minDarts returns the lower bound of darts necessary to make this map connected.
func (s *signature) minDarts() int {
	cnt := s.deg0 + s.degs.sum()
	return cnt
}

// isMaybeRealizable returns false if a map with this signature definitely cannot exist.
// It returns true if it can't tell. This is for optimization purposes, to prune
// "useless" recursion branches.
func (s *signature) isMaybeRealizable() bool {
	if s.deg0 < 0 || (s.deg0 == 0 && len(s.hole0) == 0) || s.genus < 0 {
		return false
	}
	if s.darts < s.minDarts() {
		return false
	}
	closed := s.isClosedSurface()
	if closed && s.darts%2 == 1 {
		return false
	}
	if s.innervf == IRRELEVANT {
		k := 0
		if !closed {
			k = -2
		}
		if len(s.hole0) > 0 {
			k = -3
			if len(s.holes) == 0 {
				k = -2
			}
		}
		if s.darts < (4-2*s.Chi())+len(s.holes)+k+2*len(s.degs) {
			return false
		}
		return true
	}
	if s.innervf < len(s.degs) {
		return false
	}
	if 2*s.innervf > s.darts+2*s.Chi()+len(s.holes) {
		return false
	}
	if !s.isClosedSurface() {
		return true
	}
	if 2*s.innervf-s.darts != 2*s.Chi() {
		return false
	}
	return true
}

// count enumerates maps with a given signature.
func (s *signature) count() int64 {
	sort.Ints(s.degs)
	s.holes.normalize()
	k := s.String()
	if c, ok := m[k]; ok {
		return c
	}
	if !s.isMaybeRealizable() {
		return 0
	}
	cnt := s.countInterior() + s.countExterior()
	m[k] = cnt
	zeroCount[cnt == 0]++
	return cnt
}

// reduce_Internal_EdgeIntoHole returns all signatures that can arise
// after contracting a complete root edge that starts in surface interior and ends on a boundary.
func (s signature) reduce_Internal_EdgeIntoHole() (sgns []signature) {
	if len(s.hole0) != 0 || s.deg0 <= 0 {
		return nil
	}
	s.incInnerVF(-1)
	for _, hs := range s.holes.selAll() {
		hole0s := append(hs[0].insert(), hs[0].rotate()...)
		if s.maybeNonorientable {
			n := len(hole0s)
			for i := 0; i < n; i++ {
				hole0s = append(hole0s, hole0s[i].flip())
			}
		}
		for _, nh := range hole0s {
			for d := s.deg0 - 1; d <= s.darts-s.degs.sum()-2; d++ {
				s := s
				s.deg0 = d
				s.darts -= 2
				s.hole0 = nh
				s.holes = hs[1:]
				if len(s.holes) == 0 {
					s.holes = nil
				}
				sgns = append(sgns, s)
			}
		}
	}
	return sgns
}

// reduce_Internal_EdgeIntoHole returns all signatures that can arise
// after contracting a root halfedge that starts in surface interior and ends on a boundary.
func (s signature) reduce_Internal_SemiedgeIntoHole() (sgns []signature) {
	if len(s.hole0) != 0 || s.deg0 <= 0 {
		return nil
	}
	s.incInnerVF(-1)
	for _, hs := range s.holes.selAll() {
		hole0s := append(hs[0].insert())
		if s.maybeNonorientable {
			n := len(hole0s)
			for i := 0; i < n; i++ {
				hole0s = append(hole0s, hole0s[i].flip())
			}
		}
		for _, nh := range hole0s {
			if nh[0] != (bVer{}) {
				continue
			}
			s := s
			s.deg0--
			s.darts--
			s.hole0 = nh
			s.holes = hs[1:]
			sgns = append(sgns, s)
		}
	}
	return sgns
}

// reduce_Internal_DecreaseGenus returns all signatures that can arise
// after contracting a root edge that is a loop lying in surface interior, such that
// this contraction cuts either a handle or two crosscaps.
func (s signature) reduce_Internal_DecreaseGenus() (sgns []signature) {
	if s.genus <= 0 || len(s.hole0) != 0 || (s.maybeNonorientable && s.genus == 1) {
		return nil
	}
	s.incInnerVF(+1)
	for d := 1; d <= s.deg0-3; d++ {
		s := s
		s.genus--
		if s.maybeNonorientable {
			s.genus-- // number of crosscaps
		}
		s.darts -= 2
		s.degs = append(s.degs.copy(), d)
		s.deg0 = s.deg0 - d - 2
		sgns = append(sgns, s)
	}
	return sgns
}

// reduce_Internal_CutCrosscap returns all signatures that can arise
// after contracting a root edge that is a loop lying in surface interior, such that
// this contraction cuts a crosscap.
func (s signature) reduce_Internal_CutCrosscap() []signature {
	if s.genus <= 0 || len(s.hole0) != 0 || !s.maybeNonorientable || s.deg0 < 2 {
		return nil
	}
	s.genus--
	s.deg0 -= 2
	s.darts -= 2
	return []signature{s}
}

// reduce_Internal_Split returns all signatures that can arise
// after contracting a root edge that is a loop lying in surface interior, such that
// this contraction splits a map into two maps.
func (s signature) reduce_Internal_Split() (res [][2]signature) {
	if s.genus < 0 || len(s.hole0) != 0 {
		return nil
	}
	s.darts -= 2
	s.incInnerVF(+1)
	for _, sgns := range s.split() {
		for deg := 0; deg <= s.deg0-2; deg++ {
			sgns[0].deg0 = deg
			sgns[1].deg0 = s.deg0 - 2 - deg
			res = append(res, sgns)
		}
	}
	return res
}

// countInterior counts maps with the root in the interior of the surface.
func (s signature) countInterior() (cnt int64) {
	if len(s.hole0) != 0 {
		return 0
	}
	for _, t := range s.reduce_Internal_EdgeIntoHole() {
		cnt += int64(t.deg0-s.deg0+2) * t.count()
	}
	for _, t := range s.reduce_Internal_SemiedgeIntoHole() {
		cnt += t.count()
	}
	for _, t := range s.reduce_JoinInternal() {
		cnt += t.count()
	}
	for _, t := range s.reduce_JoinInternalChosen() {
		cnt += int64(t.deg0-s.deg0+2) * t.count()
	}
	for _, t := range s.reduce_Internal_DecreaseGenus() {
		cnt += t.count()
	}
	for _, t := range s.reduce_Internal_Split() {
		cnt += t[0].count() * t[1].count()
	}
	for _, t := range s.reduce_Internal_CutCrosscap() {
		cnt += int64(s.deg0-1) * t.count()
	}
	return cnt
}

// reduce_External_AlongHole returns all signatures that can arise
// after contracting a root edge that runs along a boundary component.
func (s signature) reduce_External_AlongHole() (res []signature) {
	if len(s.hole0) == 0 || !s.hole0[0].l {
		return nil
	}
	if len(s.hole0) == 1 && s.hole0[0].r {
		s := s
		s.hole0 = nil
		s.darts--
		s.incInnerVF(+1)
		res = append(res, s)
	}
	if len(s.hole0) > 1 && s.hole0[1].r {
		for d := 0; d < s.darts-s.deg0-s.degs.sum(); d++ {
			s := s
			s.deg0 += d
			s.hole0 = append(hole{{s.hole0[1].l, s.hole0[0].r}}, s.hole0[2:]...)
			s.darts--
			res = append(res, s)
		}
	}
	for d := 0; d < s.darts-s.deg0-s.degs.sum(); d++ {
		for _, l := range []bool{true, false} {
			s := s
			s.deg0 += d
			s.hole0 = append(hole{{l, s.hole0[0].r}}, s.hole0[1:]...)
			s.darts--
			res = append(res, s)
		}
	}
	return res
}

// reduce_External_AnotherHole returns all signatures that can arise
// after contracting a root edge that joins two boundary components.
func (s signature) reduce_External_AnotherHole() (res []signature) {
	h := s.hole0
	if len(s.holes) == 0 || len(h) == 0 || h[0].l || s.deg0 <= 0 {
		return
	}
	s.hole0 = nil
	s.incInnerVF(+1)
	for _, s := range s.reduce_Internal_EdgeIntoHole() {
		nh := hole{{s.hole0[0].l, h[0].r}}
		nh = append(nh, s.hole0[1:]...)
		nh = append(nh, bVer{false, s.hole0[0].r})
		nh = append(nh, h[1:]...)
		s.hole0 = nh
		res = append(res, s)
	}
	return res
}

// reduce_External_HoleDecreaseGenus returns all signatures that can arise
// after contracting a root edge that joins two boundary components.
func (s signature) reduce_External_HoleDecreaseGenus() (res []signature) {
	if len(s.hole0) == 0 || s.hole0[0].l || s.genus <= 0 || s.deg0 <= 0 || (s.maybeNonorientable && s.genus == 1) {
		return
	}
	for _, hs := range s.hole0.split() {
		for d := s.deg0 - 1; d <= s.darts-2-s.degs.sum(); d++ {
			s := s
			s.hole0 = hs[0]
			s.holes = append(holes{hs[1]}, s.holes...)
			s.darts -= 2
			s.deg0 = d
			s.genus--
			if s.maybeNonorientable {
				s.genus--
			}
			res = append(res, s)
		}
	}
	return res
}

// reduce_External_LoopDecreaseGenus returns all signatures that can arise
// after contracting a root edge that is a loop incident to a vertex on the boundary,
// such that this contraction cuts either a handle or two crosscaps.
func (s signature) reduce_External_LoopDecreaseGenus() (res []signature) {
	if len(s.hole0) == 0 || s.hole0[0].l || s.genus <= 0 || s.deg0 <= 1 {
		return
	}
	h := s.hole0
	s.hole0 = nil
	s.incInnerVF(+1)
	for _, s := range s.reduce_Internal_DecreaseGenus() {
		s.hole0 = h
		s.incInnerVF(-1)
		res = append(res, s)
	}
	return res
}

// reduce_External_LoopCutCrosscap returns all signatures that can arise
// after contracting a root edge that is a loop incident to a vertex on the boundary,
// such that this contraction cuts a crosscap.
func (s signature) reduce_External_LoopCutCrosscap() (res []signature) {
	if len(s.hole0) == 0 || s.hole0[0].l || !s.maybeNonorientable {
		return
	}
	h := s.hole0
	s.hole0 = nil
	s.incInnerVF(+1)
	for _, t := range s.reduce_Internal_CutCrosscap() {
		t.hole0 = h
		t.incInnerVF(-1)
		res = append(res, t)
	}
	return res
}

// reduce_External_HoleCutCrosscap returns all signatures that can arise
// after contracting a root edge that joins two vertices on the same boundary component
// and goes through a crosscap.
func (s signature) reduce_External_HoleCutCrosscap() (res []signature) {
	if len(s.hole0) == 0 || s.hole0[0].l || s.deg0 <= 0 || !s.maybeNonorientable {
		return
	}
	for _, hs := range s.hole0.split() {
		hs[1] = hs[1].flip()
		h := hole{{hs[1][0].l, hs[0][0].r}}
		h = append(h, hs[1][1:]...)
		h = append(h, bVer{hs[0][0].l, hs[1][0].r})
		h = append(h, hs[0][1:]...)
		s := s
		s.hole0 = h
		s.darts -= 2
		s.genus--
		for d := s.deg0 - 1; d <= s.darts-s.degs.sum(); d++ {
			s.deg0 = d
			res = append(res, s)
		}
	}
	return res
}

// reduce_External_LoopSplit returns all signatures that can arise
// after contracting a root edge that is a loop incident to a vertex on the boundary,
// such that this contraction splits the map into two.
func (s signature) reduce_External_LoopSplit() (res [][2]signature) {
	if len(s.hole0) == 0 || s.hole0[0].l {
		return
	}
	h := s.hole0
	s.hole0 = nil
	s.incInnerVF(+1)
	for _, maps := range s.reduce_Internal_Split() {
		maps[0].hole0 = h
		maps[0].incInnerVF(-1)
		res = append(res, maps)
	}
	return res
}

// reduce_External_HoleSplit returns all signatures that can arise
// after contracting a root edge that joins two vertices on the same boundary component
// such that this contraction splits the map into two.
func (s signature) reduce_External_HoleSplit() (res [][2]signature) {
	if len(s.hole0) == 0 || s.hole0[0].l || s.deg0 <= 0 {
		return
	}
	s.darts -= 2
	for _, hs := range s.hole0.split() {
		for _, maps := range s.split() {
			maps[0].hole0 = hs[0]
			maps[1].hole0 = hs[1]
			for d0 := s.deg0 - 1; d0 <= maps[0].darts; d0++ {
				for d1 := 0; d1 <= maps[1].darts; d1++ {
					maps[0].deg0 = d0
					maps[1].deg0 = d1
					res = append(res, maps)
				}
			}
		}
	}
	return res
}

// countExterior counts maps that have a root vertex that lies on the boundary.
func (s signature) countExterior() (cnt int64) {
	if len(s.hole0) == 0 {
		return 0
	}
	if s.hole0[0].r && !s.hole0[0].l {
		s.hole0 = s.hole0.flip()
		s.holes = s.holes.flip()
	}
	for _, t := range s.reduce_External_AlongHole() {
		cnt += t.count()
	}
	for _, s := range s.reduce_External_AnotherHole() {
		cnt += s.count()
	}
	for _, s := range s.reduce_External_HoleDecreaseGenus() {
		cnt += s.count()
	}
	for _, s := range s.reduce_External_LoopDecreaseGenus() {
		cnt += s.count()
	}
	for _, s := range s.reduce_External_LoopCutCrosscap() {
		cnt += int64(s.deg0+1) * s.count()
	}
	for _, maps := range s.reduce_External_LoopSplit() {
		cnt += maps[0].count() * maps[1].count()
	}
	for _, maps := range s.reduce_External_HoleSplit() {
		cnt += maps[0].count() * maps[1].count()
	}
	for _, t := range s.reduce_External_HoleCutCrosscap() {
		cnt += t.count()
	}
	if !s.hole0[0].l {
		for _, t := range s.reduce_JoinInternal() {
			cnt += t.count()
		}
		for _, t := range s.reduce_JoinInternalChosen() {
			cnt += int64(t.deg0-s.deg0+2) * t.count()
		}
		{
			// dangling edge to a hole
			s := s
			s.darts--
			s.deg0--
			cnt += s.count()
		}
	}
	return cnt
}

// fact is factorial of n.
func fact(n int) int64 {
	if n < 0 {
		return 0
	}
	if n < 2 {
		return 1
	}
	return int64(n) * fact(n-1)
}

// pow is a to the power of b.
func pow(a, b int) int64 {
	if b == 0 {
		return 1
	}
	return int64(a) * pow(a, b-1)
}

// div divides a by b if divisible, otherwise panics.
func div(a, b int64) int64 {
	if a%b != 0 {
		panic("not divisible")
	}
	return a / b
}

// orientableMaps returns the number of maps on orientable orbifolds.
func orientableMaps(g, h, n, innervf int) (cnt int64) {
	for d := 0; d <= n; d++ {
		s := signature{
			genus:   g,
			darts:   n,
			deg0:    d,
			innervf: innervf,
		}
		for i := 0; i < h; i++ {
			s.holes = append(s.holes, hole{})
		}
		cnt += div(s.count(), fact(h))

		if h == 0 {
			continue
		}

		s = signature{
			genus:   g,
			darts:   n,
			hole0:   hole{{false, false}},
			deg0:    d,
			innervf: innervf,
		}
		for i := 0; i < h-1; i++ {
			s.holes = append(s.holes, hole{})
		}
		cnt += int64(d) * div(s.count(), fact(h-1))

		s = signature{
			genus:   g,
			darts:   n,
			hole0:   hole{{true, false}},
			deg0:    d,
			innervf: innervf,
		}
		for i := 0; i < h-1; i++ {
			s.holes = append(s.holes, hole{})
		}
		cnt += int64(2*d+1) * div(s.count(), fact(h-1))

		s = signature{
			genus:   g,
			darts:   n,
			hole0:   hole{{true, true}},
			deg0:    d,
			innervf: innervf,
		}
		for i := 0; i < h-1; i++ {
			s.holes = append(s.holes, hole{})
		}
		cnt += int64(d+1) * div(s.count(), fact(h-1))
	}
	return cnt
}

// orientableMaps returns the number of maps on non-orientable orbifolds.
func nonOrientableMaps(cc, h, n, innervf int) (cnt int64) {
	for d := 0; d <= n; d++ {
		s := signature{
			genus:              cc,
			darts:              n,
			deg0:               d,
			maybeNonorientable: true,
			innervf:            innervf,
		}
		for i := 0; i < h; i++ {
			s.holes = append(s.holes, hole{})
		}
		cnt += div(div(s.count(), fact(h)), pow(2, h))

		if h == 0 {
			continue
		}

		s = signature{
			genus:              cc,
			darts:              n,
			hole0:              hole{{false, false}},
			deg0:               d,
			maybeNonorientable: true,
			innervf:            innervf,
		}
		for i := 0; i < h-1; i++ {
			s.holes = append(s.holes, hole{})
		}
		cnt += int64(d) * div(div(s.count(), fact(h-1)), pow(2, h-1))

		s = signature{
			genus:              cc,
			darts:              n,
			hole0:              hole{{true, false}},
			deg0:               d,
			maybeNonorientable: true,
			innervf:            innervf,
		}
		for i := 0; i < h-1; i++ {
			s.holes = append(s.holes, hole{})
		}
		cnt += int64(2*d+1) * div(div(s.count(), fact(h-1)), pow(2, h-1))

		s = signature{
			genus:              cc,
			darts:              n,
			hole0:              hole{{true, true}},
			deg0:               d,
			maybeNonorientable: true,
			innervf:            innervf,
		}
		for i := 0; i < h-1; i++ {
			s.holes = append(s.holes, hole{})
		}
		cnt += int64(d+1) * div(div(s.count(), fact(h-1)), pow(2, h-1))
	}
	if cc%2 == 0 {
		cnt -= orientableMaps(cc/2, h, n, innervf)
	}
	return cnt
}

// distrbp it a multinomial coefficient, the number of ways to choose:
// v1 out of vf initial distinct elements,
// then v2 out of the remaining elements,
// ...,
// finally vk out of the remaining elements.
// Here v1, v2, ..., vk are the values in m.
func distrbp(vf int, m map[int]int) (res int64) {
	res = 1
	for _, cnt := range m {
		if cnt > vf {
			return 0
		}
		res *= fact(vf) / fact(cnt) / fact(vf-cnt)
		vf -= cnt
	}
	return res
}

// countOnOrbifold enumerates maps with a given number of darts on a given orbifold,
// which is characterized by its orientability, Euler characteristics,
// the number of boundary components, and branch point indices.
func countOnOrbifold(darts int, orientable bool, chi, h int, bp ...int) (cnt int64) {
	m := map[int]int{}
	for _, mi := range bp {
		m[mi]++
	}
	for vf := 0; vf <= darts+1; vf++ {
		if len(bp) == 0 {
			vf = IRRELEVANT
		}
		if orientable {
			cnt += orientableMaps((2-chi-h)/2, h, darts, vf) * distrbp(vf, m)
		} else {
			cnt += nonOrientableMaps(2-chi-h, h, darts, vf) * distrbp(vf, m)
		}
		if len(bp) == 0 {
			break
		}
	}
	m2 := m[2]
	for i := 1; i <= m2; i++ {
		if h > 0 {
			panic("holes and deg 2 branch points")
		}
		m[2] = m2 - i
		if darts%2 != i%2 || i >= darts {
			continue
		}
		darts := darts - i
		vf := chi + darts/2
		insertDangling := fact(darts+i-1) / fact(i) / fact(darts-1)
		var maps int64
		if orientable {
			maps = orientableMaps((2-chi-h)/2, 0, darts, IRRELEVANT)
		} else {
			maps = nonOrientableMaps(2-chi-h, 0, darts, IRRELEVANT)
		}
		cnt += maps * distrbp(vf, m) * int64(insertDangling) * int64(darts+i) / int64(darts)
	}
	return cnt
}

var (
	genus = flag.Int("genus", 5, "Genus to compute up to.")
	edges = flag.Int("edges", 10, "The number of edges to compute up to.")
)

func main() {

	defer func(t time.Time) {
		fmt.Println(time.Now().Sub(t))
		//fmt.Println(zeroCount)
	}(time.Now())

	wd, err := os.Getwd()
	if err != nil {
		fmt.Println(err)
		os.Exit(1)
	}
	const file = "o_r_orbilfolds.txt"
	data, err := ioutil.ReadFile(path.Join(wd, file))
	if err != nil {
		fmt.Println(err)
		os.Exit(1)
	}
	cnt := make([][]int64, *edges+1)
	for _, ln := range strings.Split(string(data), "\n") {
		if strings.Trim(ln, " ") == "" || strings.HasPrefix(ln, "#") {
			continue
		}
		var G, L, Chi, H int
		var signStr string
		if _, err := fmt.Sscanf(ln, "%d%d%s%d%d ", &G, &L, &signStr, &Chi, &H); err != nil {
			fmt.Println(err)
			os.Exit(1)
		}
		if G > *genus {
			continue
		}
		splits := strings.Split(strings.Split(ln, "[")[2], "]")
		var m []int
		if mStr := splits[0]; mStr != "" {
			for _, n := range strings.Split(mStr, " ") {
				i, err := strconv.Atoi(n)
				if err != nil {
					panic(fmt.Sprintf("%q: %s", mStr, err))
				}
				m = append(m, i)
			}
		}
		var Epi int64
		if _, err := fmt.Sscanf(splits[1], "%d", &Epi); err != nil {
			panic(fmt.Sprintf("%q: %s", splits[1], err))
		}
		for e := 0; e <= *edges; e++ {
			//t := time.Now()
			for len(cnt[e]) <= *genus {
				cnt[e] = append(cnt[e], 0)
			}
			if (2*e)%L != 0 {
				continue
			}
			val := Epi * countOnOrbifold(2*e/L, signStr == "[+]", Chi, H, m...)
			//fmt.Println(e, 2*e/L, signStr == "[+]", Chi, H, m, "====", val, int64(time.Now().Sub(t))/1e6)
			cnt[e][G] += val
		}
	}
	fmt.Println(`# Reflexible maps with E edges on orientable surfaces of genus G.
# Unsensed maps = (sensed maps + reflexible maps) / 2.
`)
	for i, byGenus := range cnt {
		if i == 0 {
			fmt.Printf("%15s", "E\\G")
			for g := range byGenus {
				fmt.Printf("%15d", g)
			}
		} else {
			fmt.Printf("%15d", i)
			for _, c := range byGenus {
				fmt.Printf("%15d", div(c, 2*int64(i)))
			}
		}
		fmt.Println()
	}
}
