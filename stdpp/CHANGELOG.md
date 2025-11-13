This file lists "large-ish" changes to the std++ Coq library, but not every
API-breaking change is listed.

## std++ master

The opam packages have been renamed from `coq-*` to `rocq-*`.

This version of std++ newly supports Rocq 9.1.

- Declare the internals of `coPset` as `Local`.
- Improve documentation of `coPset`. (by François Pottier)
- Add lemma `map_fmap_imap`. (by Rudy Peterson)
- Generalize `gmap_curry`, `gmap_uncurry` to any finite map as `map_curry`,
  `map_uncurry`. (by Isaac van Bakel)
- Replace all `gmap_curry`, `gmap_uncurry` lemmas with generalized versions
  which apply to `map_curry`, `map_uncurry`. These have the same naming scheme
  as their `gmap` versions, just with `map` instead.
- Add lemmas `map_to_list_kmap` and `kmap_list_to_map`. (by Rudy Peterson)
- Add lemmas `list_to_set_fmap` and `list_to_set_fmap_L`. (by Rudy Peterson)
- Add lemmas `list_to_set_singleton_L` and `list_to_set_snoc_L`. (by Rudy Peterson)
- Add lemmas `elem_of_sublist`, `singleton_sublist_l` and `sublist_NoDup`.
  (by Kimaya Bedarkar)
- Add instances `map_seq_inj` and `map_seqZ_inj`, and lemmas
  `map_seq_list_to_map`, `map_seq_to_list`, `map_seqZ_list_to_map` and
  `map_seqZ_to_list`. (by Rudy Peterson)
- Add lemmas `take_nil_inv` and `drop_nil_inv`. (by Kimaya Bedarkar)
- Add `app_nil_r_inv` and `app_nil_l_inv` lemmas. (by Kimaya Bedarkar)
- Add definition `powermset` and associated lemmas. (by Marijn van Wezel)
- Add lemmas `interleave_middle` and `elem_of_interleave`. (by Marijn van Wezel)
- Add lemma `map_to_list_update`. (by Rudy Peterson)
- Add `lookup_union_list_None` and `lookup_union_list_Some`. (by Rudy Peterson)
- Add `map_disjoint_list` to express that all maps in a list are pair-wise
  disjoint from each other, add some lemmas about this definition. (by Rudy
  Peterson)
- Add `Hint Mode` for `Cancel` class.
- Adjust the `lookup` and `lookup_total` lemmas for lists and maps to cover the
  "eq" and "ne" case in a single lemma statement.
  + The new lemmas are of the form
    `lookup_op : op .. i !! j = if decide (i = j) then .. else ..`, e.g.,
    `lookup_delete : delete i m !! j = if decide (i = j) then None else m !! j`.
    These lemmas are convenient because proofs of the form:
    `destruct (decide (i = j)). { rewrite lookup_op_eq .. } { rewrite lookup_op_ne .. }`
    can often be shortened to `rewrite lookup_op; case_decide`.
  + The original lemma `lookup_op : op .. i !! i = ...` is renamed into
    `lookup_op_eq`. For example, `lookup_delete` becomes `lookup_delete_eq`.
    A full list of renames can be found in the `sed` script.
  + The original lemma `lookup_op_ne : op .. i !! j = ...` is unaffected.
- Rename `multiplicity_singleton` → `multiplicity_singleton_eq` and
  `multiplicity_singleton'` → `multiplicity_singleton`. That is, the lemma
  `multiplicity_singleton` becomes the version with `decide` in order to be
  consistent with the `lookup` lemmas.
- Adjust the "commuting" lemmas for lists and maps to cover the "eq" and "ne"
  case in a single lemma statement.
  + The new lemmas are of the form
    `op1_op2 : op1 .. i (op2 .. j) = if decide (i = j) then .. else ..`, e.g.,
   `insert_delete <[i:=x]> (delete j m) = if decide (i = j) then <[i:=x]> m else delete j (<[i:=x]> m)`.
  + Consistently provide versions `op1_op2_eq` and `op1_op2_ne`. For example,
    `insert_delete_eq : <[i:=x]> (delete i m) = <[i:=x]> m` and
    `insert_delete_ne : i ≠ j → <[i:=x]> (delete j m) = delete j (<[i:=x]> m)`.
  + For maps, lemmas have been added for all combinations of `op1` being
    `partial_alter`, `alter`, `delete` and `insert`; and `op2` being any of the
    aforementioned operations or `singleton`.
  + Existing lemmas have been renamed to follow the new scheme:
    `partial_alter_compose` → `partial_alter_partial_alter_eq` (direction also
    changed),
    `partial_alter_commute` → `partial_alter_partial_alter_ne`,
    `alter_compose` → `alter_alter_eq` (direction also changed),
    `alter_commute` → `alter_alter_ne`.
    `delete_commute` → `delete_delete` (no `_ne` suffix because the lemmas holds
    without `≠` premise),
    `delete_idemp` → `delete_delete_eq`,
    `insert_insert` → `insert_insert_eq`,
    `insert_commute` → `insert_insert_ne`,
    `alter_insert` → `alter_insert_eq`,
    `delete_insert_delete` → `delete_insert_eq`,
    `delete_alter` → `delete_alter_eq`,
    `insert_delete_insert` → `insert_delete_eq`,
    `delete_insert_delete` → `delete_insert_eq`,
    `delete_alter` → `delete_alter_eq`,
    `insert_delete_insert` → `insert_delete_eq`,
    `delete_alter` → `delete_alter_eq`,
    `alter_singleton` → `alter_singleton_eq`,
    `delete_singleton` → `delete_singleton_eq`,
    `insert_singleton` → `insert_singleton_eq`,
    `foldr_delete_commute` → `delete_foldr_delete`,
    `list_insert_insert` → `list_insert_insert_eq`,
    `list_insert_commute` → `list_insert_insert_ne`,
    `list_alter_compose` → `list_alter_alter_eq` (direction also changed),
    `list_alter_commute` → `list_alter_alter_eq`,
    `take_insert` → `take_insert_ge`,
    `take_alter` → `take_alter_ge`,
    `drop_alter` → `drop_alter_lt`.
  + Add `alter_app` and `insert_app`.
  + Other related renames:
    `foldr_delete_insert` → `foldr_delete_insert_in`
    `foldr_delete_insert_ne` → `foldr_delete_insert_notin`.
- The names `op1_op2` were sometimes used for lemmas of the shape
  `.. → op1 .. (op2 .. m) = m`. These lemmas are now called `op1_op2_id`
  (because they are the "identity", but that requires preconditions to hold):
  `partial_alter_self_alt` → `partial_alter_id` (also became stronger, but
  should be backwards compatible),
  `delete_notin` → `delete_id`,
  `delete_insert` → `delete_insert_id`,
  `insert_delete` → `insert_delete_id`,
  `foldr_delete_notin` → `foldr_delete_id`.
- Add lemma `partial_alter_id`.
- Rename `lookup_delete_lt` → `list_lookup_delete_lt`,
  `lookup_delete_ge` → `list_lookup_delete_ge`,
  `lookup_total_delete_lt` → `list_lookup_total_delete_lt`
  `lookup_total_delete_ge` → `list_lookup_total_delete_ge`.
  The `list_` suffix is needed to avoid conflicts with the map lemmas.
- Add lemmas `list_lookup_delete` and `list_lookup_total_delete` that combine
  both versions.
- Rename `drop_insert_le` → `drop_insert_ge` and `drop_insert_gt` →
  `drop_insert_lt` to make the direction of the inequality consistent with the
  `take` lemmas.
- Add lemmas `lookup_singleton_is_Some`, `list_lookup_insert_is_Some`,
  `list_lookup_insert_None`.
- Rename lemmas `elem_of_list_X` into `list_elem_of_X` to be consistent with
  the `list_lookup_X` lemmas. The `sed` script contains all renames, the
  following renames were special since they fix other inconsistencies:
  `list_elem_of_fmap_1` → `list_elem_of_fmap_2`,
  `list_elem_of_fmap_1_alt` → `list_elem_of_fmap_2'`,
  `list_elem_of_fmap_2` → `list_elem_of_fmap_1`,
  `list_lookup_fmap_inv` → `list_lookup_fmap_Some_1`,
  `list_elem_of_fmap_2_inj` → `list_elem_of_fmap_inj_2`.
- Change the order of the conjunction in `list_lookup_fmap_Some`. The new
  version is `(f <$> l) !! i = Some y ↔ ∃ x, y = f x ∧ l !! i = Some x`, which
  makes it consistent with `list_elem_of_fmap` and the corresponding lemmas for
  sets and maps.
- Rename `list_alter_fmap` → `list_fmap_alter`.
- Remove `list_alter_fmap_mono`, use `list_fmap_alter` instead.
- Add several lemmas for `map_difference` that already existed for
  sets. (by Johannes Hostert)
- Add set lemma `empty_difference`. (by Johannes Hostert)
- Rename `map_disjoint_difference_l` (and `_r`) into `map_disjoint_difference_l1`
  for consistency with the `disjoint_difference_l1` lemma on sets.
- Add lemmas `Forall_exists_Forall2_{l,r}`. (by Rudy Peterson)
- Add lemmas `zip_with_nil_l`, `NoDup_zip_with_{l,r}_strong`,
  `NoDup_zip_with_{l,r}`, `zip_nil_{l,r}`, `prod_map_zip` and `NoDup_zip_{l,r}`.
  (by Rudy Peterson)
- Provide support for `is_Some None` in the tactics `done` and `naive_solver`.
- Add lemmas `alter_id'`, `alter_id_dom`, `alter_alt`, `alter_alt_Some` and
- Generalize assumption of lemma `const_fmap`. (by Kimaya Bedarkar)
- Add lemmas `list_elem_of_delete_inv`, `list_elem_of_foldr_delete_inv`,
  `sublist_app_cons_r`, `sublist_app_cons_l`, `sublist_subseteq` and
  `sublist_filter`. (by Jonas Kastberg Hinrichsen)
- Rename `list_delete_subseteq` → `list_subseteq_delete` and
  `list_filter_subseteq` → `list_subseteq_filter`.
- Add `Hint Mode` with `- !` for `Reflexive`, `Symmetric`, `Transitive`,
  `PreOrder` and `Equivalence`.
- Add lemmas `sum_list_with_foldr`/`max_list_with_foldr` that show
  correspondence between `sum_list`/`max_list` and `foldr`. (by Sanjit Bhat)
- Add `Proper` instances for `sum_list`/`max_list` under `Permutation`.
  (by Sanjit Bhat)
- Make `sum_list_with` and `max_list_with` opaque for type classes.
- Make `list_union` and `list_dist_union` opaque for type classes.
- Rename instance `gmultiset_disj_union_list_proper` →
  `gmultiset_disj_union_list_permutation_proper` to ensure consistency with sets.
- Add lemmas `list_filter_singleton`, `list_filter_singleton_True` and
  `list_filter_singleton_False`.
- Rename lemmas `filter_singleton` → `filter_singleton_True` and
  `filter_singleton_not` → `filter_singleton_False`, and add unified lemma
  `filter_singleton` based on `decide`. This makes the filter lemmas for
  singleton sets consistent with those for maps and lists.
- Strengthen `coPpick_elem_of` to have premise `X ≠ ∅` instead of `¬set_finite X`.
- Rename `coPset_suffixes_infinite` → `coPset_suffixes_not_finite` and
  `nclose_infinite` → `nclose_not_finite`, these lemmas are about `set_finite`.
  Re-purpose `coPset_suffixes_infinite` and `nclose_infinite` for lemmas about
  `set_infinite`.
- Add lemma `nclose_non_empty`.
- Allow recursive calls after applying `map_Forall_impl` by making it
  `Defined`. (by Simcha van Collem)
- Extend `set_solver` with support for `Pset_to_coPset` and `gset_to_coPset`.
- Add lemma `set_infinite_non_empty`.
- Make `namespace` a newtype so it is no longer convertible to `list positive`
  and thereby exposes the internal representation.
- Add instance `Inhabited (∀ x, B x)`. The old instance `impl_inhabited` for
  `Inhabited (A → B)` has been removed, as the one for `∀` generalizes it. (by
  Jan-Oliver Kaiser)
- Add `Filter` instance for `gmultiset`, along with the corresponding lemmas
  for `gmultiset` operations, `elem_of`, `subseteq` and `multiplicity`.
  (by Egor Namakonov)
- Extend the `multiset_solver` tactic to support the `filter` operation.
- Remove the dependency of the class `TopSet` on `Set_` (and hence the
  dependency on `Intersection` and `Difference`). (by Simcha van Collem)
- Add the type `topGset` of finite sets with a top element. (by Simcha van
  Collem)
- Remove superfluous `Infinite` premise from `gset_to_coGset_finite`.
- Add lemmas `map_Forall2_flip` and `option_Forall2_flip`.
- Add lemmas `map_Forall2_union_inv_{l,r}`. (inspired by Tesla Zhang)
- Add instances for `EqDecision` and `Countable` for `sigT` types. (by Tesla
  Zhang)

**Changes in `stdpp_bitvector`:**

- Add support for bitwise reasoning about `bv_swrap`. (by Brian Campbell)

The following `sed` script should perform most of the renaming
(on macOS, replace `sed` by `gsed`, installed via e.g. `brew install gnu-sed`).
Note that the script is not idempotent, do not run it twice.
```
sed -i -E -f- $(find theories -name "*.v") <<EOF
# gmap_curry/uncurry
s/\bgmap_curry\b/map_curry/g
s/\bgmap_uncurry\b/map_uncurry/g
s/\blookup_gmap_uncurry\b/lookup_map_uncurry/g
s/\blookup_gmap_curry\b/lookup_map_curry/g
s/\blookup_gmap_curry_None\b/lookup_map_curry_None/g
s/\bgmap_uncurry_curry\b/map_uncurry_curry/g
s/\bgmap_curry_non_empty\b/map_curry_non_empty/g
s/\bgmap_curry_uncurry_non_empty\b/map_curry_uncurry_non_empty/g

# map _eq lookup lemmas
s/\blookup_partial_alter\b/lookup_partial_alter_eq/g
s/\blookup_total_partial_alter\b/lookup_total_partial_alter_eq/g
s/\blookup_alter\b/lookup_alter_eq/g # total_lookup_version was missing, added
s/\blookup_delete\b/lookup_delete_eq/g
s/\blookup_total_delete\b/lookup_total_delete_eq/g
s/\blookup_insert\b/lookup_insert_eq/g
s/\blookup_total_insert\b/lookup_total_insert_eq/g
s/\blookup_singleton\b/lookup_singleton_eq/g
s/\blookup_total_singleton\b/lookup_total_singleton_eq/g

# map _eq commute lemmas
s/\bpartial_alter_compose\b/partial_alter_partial_alter_eq/g # direction changed
s/\bpartial_alter_commute\b/partial_alter_partial_alter_ne/g
s/\balter_compose\b/alter_alter_eq/g # direction changed
s/\balter_commute\b/alter_alter_ne/g
s/\bdelete_commute\b/delete_delete/g # no _ne since no ≠ premise is needed
s/\bdelete_idemp\b/delete_delete_eq/g
s/\binsert_insert\b/insert_insert_eq/g
s/\binsert_commute\b/insert_insert_ne/g
s/\balter_insert\b/alter_insert_eq/g
s/\bdelete_insert\b/delete_insert_id/g # Has m !! i = None premise, and gives .. = m
s/\bdelete_insert_delete\b/delete_insert_eq/g
s/\bdelete_alter\b/delete_alter_eq/g
s/\binsert_delete_insert\b/insert_delete_eq/g
s/\binsert_delete\b/insert_delete_id/g # Has m !! i = Some .. premise, and gives .. = m
s/\bdelete_alter\b/delete_alter_eq/g
s/\balter_singleton\b/alter_singleton_eq/g
s/\bdelete_singleton\b/delete_singleton_eq/g
s/\binsert_singleton\b/insert_singleton_eq/g
s/\bfoldr_delete_commute\b/delete_foldr_delete/g
s/\bfoldr_delete_notin\b/foldr_delete_id/g
s/\bfoldr_delete_insert\b/foldr_delete_insert_in/g
s/\bfoldr_delete_insert_ne\b/foldr_delete_insert_notin/g

# map misc changes
s/\bdelete_notin\b/delete_id/g # instance of partial_alter_id
s/\bpartial_alter_self_alt\b/partial_alter_id/g # also became stronger, but should be backwards compatible

# _eq lemmas for multiset
s/\bmultiplicity_singleton\b/multiplicity_singleton_eq/g
s/\bmultiplicity_singleton'\b/multiplicity_singleton/g

# list _eq lookup lemmas
s/\blist_lookup_insert\b/list_lookup_insert_eq/g
s/\blist_lookup_total_insert\b/list_lookup_total_insert_eq/g
s/\blist_lookup_alter\b/list_lookup_alter_eq/g
s/\blist_lookup_total_alter\b/list_lookup_total_alter_eq/g
s/\blookup_delete_lt\b/list_lookup_delete_lt/g
s/\blookup_delete_ge\b/list_lookup_delete_ge/g
s/\blookup_total_delete_lt\b/list_lookup_total_delete_lt/g
s/\blookup_total_delete_ge\b/list_lookup_total_delete_ge/g
s/\blookup_take\b/lookup_take_lt/g
s/\blookup_total_take\b/lookup_total_take_lt/g

# list _eq commute lemmas
s/\blist_insert_insert\b/list_insert_insert_eq/g
s/\blist_insert_commute\b/list_insert_insert_ne/g
s/\blist_alter_compose\b/list_alter_alter_eq/g # direction changed
s/\blist_alter_commute\b/list_alter_alter_eq/g
s/\btake_insert\b/take_insert_ge/g
s/\btake_alter\b/take_alter_ge/g
s/\bdrop_alter\b/drop_alter_lt/g
s/\bdrop_insert_le\b/drop_insert_ge/g # make inequality consistent with take lemma
s/\bdrop_insert_gt\b/drop_insert_lt/g # make inequality consistent with take lemma

# list_elem_of
s/\bdecompose_elem_of_list\b/decompose_list_elem_of/g
s/\belem_of_list\b/list_elem_of/g
s/\belem_of_list_here\b/list_elem_of_here/g
s/\belem_of_list_further\b/list_elem_of_further/g
s/\belem_of_list_In\b/list_elem_of_In/g
s/\belem_of_list_singleton\b/list_elem_of_singleton/g
s/\belem_of_list_lookup_1\b/list_elem_of_lookup_1/g
s/\belem_of_list_lookup_total_1\b/list_elem_of_lookup_total_1/g
s/\belem_of_list_lookup_2\b/list_elem_of_lookup_2/g
s/\belem_of_list_lookup_total_2\b/list_elem_of_lookup_total_2/g
s/\belem_of_list_lookup\b/list_elem_of_lookup/g
s/\belem_of_list_lookup_total\b/list_elem_of_lookup_total/g
s/\belem_of_list_split_length\b/list_elem_of_split_length/g
s/\belem_of_list_split\b/list_elem_of_split/g
s/\belem_of_list_split_l\b/list_elem_of_split_l/g
s/\belem_of_list_split_r\b/list_elem_of_split_r/g
s/\belem_of_list_intersection_with\b/list_elem_of_intersection_with/g
s/\belem_of_list_difference\b/list_elem_of_difference/g
s/\belem_of_list_union\b/list_elem_of_union/g
s/\belem_of_list_intersection\b/list_elem_of_intersection/g
s/\belem_of_list_filter\b/list_elem_of_filter/g
s/\belem_of_list_fmap\b/list_elem_of_fmap/g
s/\belem_of_list_fmap_1\b/list_elem_of_fmap_2/g
s/\belem_of_list_fmap_2\b/list_elem_of_fmap_1/g
s/\belem_of_list_fmap_1_alt\b/list_elem_of_fmap_2'/g
s/\belem_of_list_fmap_inj\b/list_elem_of_fmap_inj/g
s/\belem_of_list_fmap_2_inj\b/list_elem_of_fmap_inj_2/g
s/\belem_of_list_omap\b/list_elem_of_omap/g
s/\belem_of_list_bind\b/list_elem_of_bind/g
s/\belem_of_list_ret\b/list_elem_of_ret/g
s/\belem_of_list_join\b/list_elem_of_join/g
s/\belem_of_list_dec\b/list_elem_of_dec/g

# list fmap lemmas
s/\blist_lookup_fmap_inv\b/list_lookup_fmap_Some_1/g
s/\blist_alter_fmap\b/list_fmap_alter/g
s/\blist_alter_fmap_mono\b/list_fmap_alter/g

# map_disjoint_difference_{l|r}
s/\bmap_disjoint_difference_l\b/map_disjoint_difference_l1/g
s/\bmap_disjoint_difference_r\b/map_disjoint_difference_r1/g

# list subseteq
s/\blist_delete_subseteq\b/list_subseteq_delete/g
s/\blist_filter_subseteq\b/list_subseteq_filter/g

# gmultiset disj union proper
s/\bgmultiset_disj_union_list_proper\b/gmultiset_disj_union_list_permutation_proper/g

# filter
s/\bfilter_singleton\b/filter_singleton_True/g
s/\bfilter_singleton_not\b/filter_singleton_False/g

# set_infinite
s/\bcoPset_suffixes_infinite\b/coPset_suffixes_not_finite/g
s/\bnclose_infinite\b/nclose_not_finite/g
EOF
```

## std++ 1.12.0 (2025-06-04)

std++ 1.12 supports Coq 8.18, 8.19, 8.20, and Rocq 9.0.

This released of std++ was managed by Jesper Bengtson, Ralf Jung,
and Robbert Krebbers, with contributions from Andres Erbsen, Kimaya Bedarkar,
Marijn van Wezel, Michael Sammler, Ralf Jung, Robbert Krebbers, Rodolphe Lepigre,
Rudy Peterson, and Marijn van Wezel. Thanks a lot to everyone involved.

**Detailed list of changes:**

- Add lemmas `Forall_vinsert` and `Forall_vreplicate`. (by Rudy Peterson)
- Add `disj_union_list` and associated lemmas for `gmultiset`. (by Marijn van Wezel)
- Add lemma `lookup_total_fmap`.
- Add lemmas about `last` and `head`: `last_app_Some`, `last_app_None`,
  `head_app_Some`, `head_app_None` and `head_app`. (by Marijn van Wezel)
- Rename `map_filter_empty_iff` to `map_empty_filter` and add
  `map_empty_filter_1` and `map_empty_filter_2`. (by Michael Sammler)
- Add lemma about `zip_with`: `lookup_zip_with_None` and add lemmas for `zip`:
 `length_zip`, `zip_nil_inv`, `lookup_zip_Some`,`lookup_zip_None`. (by Kimaya Bedarkar)
- Add `elem_of_seq` and `seq_nil`. (by Kimaya Bedarkar)
- Add lemmas `StronglySorted_app`, `StronglySorted_cons` and
  `StronglySorted_app_2`. Rename lemmas
  `elem_of_StronglySorted_app` → `StronglySorted_app_1_elem_of`,
  `StronglySorted_app_inv_l` → `StronglySorted_app_1_l`
  `StronglySorted_app_inv_r` → `StronglySorted_app_1_r`. (by Marijn van Wezel)
- Add `SetUnfoldElemOf` instance for `dom` on `gmultiset`. (by Marijn van Wezel)
- Split up `stdpp.list` into smaller files. Users should keep importing
  `stdpp.list`; the organization into smaller modules is considered an
  implementation detail. `stdpp.list_numbers` is now re-exported by `stdpp.list`
  and also considered part of the list module, so existing imports should be
  updated.
- Remove `list_remove` and `list_remove_list`. There were no lemmas about these
  functions; they existed solely to facilitate the proofs of decidability of
  `submseteq` and `≡ₚ`, which have been refactored.

The following `sed` script should perform most of the renaming
(on macOS, replace `sed` by `gsed`, installed via e.g. `brew install gnu-sed`).
Note that the script is not idempotent, do not run it twice.
```
sed -i -E -f- $(find theories -name "*.v") <<EOF
# length
s/\bmap_filter_empty_iff\b/map_empty_filter/g
# StronglySorted
s/\belem_of_StronglySorted_app\b/StronglySorted_app_1_elem_of/g
s/\bStronglySorted_app_inv_(l|r)\b/StronglySorted_app_1_\1/g
EOF
```

## std++ 1.11.0 (2024-10-30)

The highlights of this release include:
* support for building with dune
* stronger versions of the induction principles for `map_fold`, exposing the order in
  which elements are processed

std++ 1.11 supports Coq 8.18, 8.19 and 8.20.
Coq 8.16 and 8.17 are no longer supported.

This release of std++ was managed by Jesper Bengtson, Ralf Jung, 
and Robbert Krebbers, with contributions from Andres Erbsen, Lennard Gäher, 
Léo Stefanesco, Marijn van Wezel, Paolo G. Giarrusso, Pierre Roux,
Ralf Jung, Robbert Krebbers, Rodolphe Lepigre, Sanjit Bhat, Yannick Zakowski, 
and Yiyun Liu. Thanks a lot to everyone involved!


**Detailed list of changes:**

- Generalize `foldr_comm_acc`, `map_fold_comm_acc`, `set_fold_comm_acc`, and
  `gmultiset_set_fold_comm_acc` to have more general type. (by Yannick Zakowski)
- Strengthen `map_disjoint_difference_l` and `map_disjoint_difference_l`, and
  thereby make them consistent with the corresponding lemmas for sets.
- Add support for compiling the packages with dune. (by Rodolphe Lepigre)
- Add lemmas `gset_to_gmap_singleton`, `difference_union_intersection`,
  `difference_union_intersection_L`. (by Léo Stefanesco)
- Make the build script compatible with BSD systems. (by Yiyun Liu)
- Rename lemmas `X_length` into `length_X`, see the sed script below for an
  overview. This follows https://github.com/coq/coq/pull/18564.
- Redefine `map_imap` so its closure argument can contain recursive
  occurrences of a `Fixpoint`.
- Add lemma `fmap_insert_inv`.
- Rename `minimal_exists` to `minimal_exists_elem_of` and
  `minimal_exists_L` to `minimal_exists_elem_of_L`.
  Add new `minimal_exists` lemma. (by Lennard Gäher)
- Generalize `map_relation R P Q` to have the key (extra argument `K`) in the
  predicates `R`, `P` and `Q`.
- Generalize `map_included R` to a predicate `R : K → A → B → Prop`, i.e., (a)
  to have the key, and (b) to have different types `A` and `B`.
- Add `map_Forall2` and some basic lemmas about it.
- Rename `map_not_Forall2` into `map_not_relation`.
- Replace the induction principle `map_fold_ind` for `map_fold` with a stronger
  version:
  + The main new induction principle is `map_first_key_ind`, which is meant
    to be used together with the lemmas `map_fold_insert_first_key` and
    `map_to_list_insert_first_key` (and others about `map_first_key`). This
    induction scheme reflects all these operations (induction, `map_fold`,
    `map_to_list`) process the map in the same order.
  + The new primitive induction principle `map_fold_fmap_ind` is only relevant
    for implementers of `FinMap` instances.
  + The lemma `map_fold_foldr` has been strengthened to (a) drop the
    commutativity requirement and (b) give an equality (`=`) instead of being
    generic over a relation `R`.
  + The lemma `map_to_list_fmap` has been strengthened to give an equality (`=`)
    instead of a permutation (`≡ₚ`).
  + The lemmas `map_fold_comm_acc_strong` and `map_fold_comm_acc` have been
    strengthened to only require commutativity w.r.t. the operation being
    pulled out of the accumulator, not commutativity of
    the folded function itself.
- Add lemmas `Sorted_unique_strong` and `StronglySorted_unique_strong` that only
  require anti-symmetry for the elements that are in the list.
- Rename `foldr_cons_permute` into `foldr_cons_permute_strong` and strengthen
  (a) from function `f : A → A → A` to `f : A → B → B`, and (b) to only require
  associativity/commutativity for the elements that are in the list.
- Rename `foldr_cons_permute_eq` into `foldr_cons_permute`.
- Various improvements to the support of strings:
  + Add string literal notation "my string" to `std_scope`, and no longer
    globally open `string_scope`.
  + Move all definitions and lemmas about strings/ascii into the modules
    `String`/`Ascii`, i.e., rename `string_rev_app` → `String.rev_app`,
    `string_rev` → `String.rev`, `is_nat` → `Ascii.is_nat`,
    `is_space` → `Ascii.is_space` and `words` → `String.words`.
  + The file `std.strings` no longer exports the `String` module, it only
    exports the `string` type, its constructors, induction principles, and
    notations (in `string_scope`). Similar to the number types (`nat`, `N`,
    `Z`), importing the `String` module yourself is discouraged, rather use
    `String.function` and `String.lemma`.
  + Add `String.le` and some theory about it (decidability, proof irrelevance,
    total order).
- Add lemmas `foldr_idemp_strong` and `foldr_idemp`.
- Add lemmas `set_fold_union_strong` and `set_fold_union`.
- Add lemmas `map_fold_union_strong`, `map_fold_union`,
  `map_fold_disj_union_strong`, `map_fold_disj_union` and `map_fold_proper`.
- Add `gmultiset_map` and associated lemmas. (by Marijn van Wezel)
- Add `CProd` type class for Cartesian products; with instances for `list`,
  `gset`, `boolset`, `MonadSet` (i.e., `propset`, `listset`); and `set_solver`
  tactic support. (by Thibaut Pérami)

The following `sed` script should perform most of the renaming
(on macOS, replace `sed` by `gsed`, installed via e.g. `brew install gnu-sed`).
Note that the script is not idempotent, do not run it twice.
```
sed -i -E -f- $(find theories -name "*.v") <<EOF
# length
s/\bnil_length\b/length_nil/g
s/\bcons_length\b/length_cons/g
s/\bapp_length\b/length_app/g
s/\bmap_to_list_length\b/length_map_to_list/g
s/\bseq_length\b/length_seq/g
s/\bseqZ_length\b/length_seqZ/g
s/\bjoin_length\b/length_join/g
s/\bZ_to_little_endian_length\b/length_Z_to_little_endian/g
s/\balter_length\b/length_alter/g
s/\binsert_length\b/length_insert/g
s/\binserts_length\b/length_inserts/g
s/\breverse_length\b/length_reverse/g
s/\btake_length\b/length_take/g
s/\btake_length_le\b/length_take_le/g
s/\btake_length_ge\b/length_take_ge/g
s/\bdrop_length\b/length_drop/g
s/\breplicate_length\b/length_replicate/g
s/\bresize_length\b/length_resize/g
s/\brotate_length\b/length_rotate/g
s/\breshape_length\b/length_reshape/g
s/\bsublist_alter_length\b/length_sublist_alter/g
s/\bmask_length\b/length_mask/g
s/\bfilter_length\b/length_filter/g
s/\bfilter_length_lt\b/length_filter_lt/g
s/\bfmap_length\b/length_fmap/g
s/\bmapM_length\b/length_mapM/g
s/\bset_mapM_length\b/length_set_mapM/g
s/\bimap_length\b/length_imap/g
s/\bzip_with_length\b/length_zip_with/g
s/\bzip_with_length_l\b/length_zip_with_l/g
s/\bzip_with_length_l_eq\b/length_zip_with_l_eq/g
s/\bzip_with_length_r\b/length_zip_with_r/g
s/\bzip_with_length_r_eq\b/length_zip_with_r_eq/g
s/\bzip_with_length_same_l\b/length_zip_with_same_l/g
s/\bzip_with_length_same_r\b/length_zip_with_same_r/g
s/\bnatset_to_bools_length\b/length_natset_to_bools/g
s/\bvec_to_list_length\b/length_vec_to_list/g
s/\bfresh_list_length\b/length_fresh_list/g
s/\bbv_to_little_endian_length\b/length_bv_to_little_endian/g
s/\bbv_seq_length\b/length_bv_seq/g
s/\bbv_to_bits_length\b/length_bv_to_bits/g
# renaming of minimal_exists
s/\bminimal_exists_L\b/minimal_exists_elem_of_L/g
s/\bminimal_exists\b/minimal_exists_elem_of/g
# map_relation
s/\bmap_not_Forall2\b/map_not_relation/g
# map_fold
s/\bmap_fold_ind2\b/map_fold_weak_ind/g
# foldr_cons_permute
s/\bfoldr_cons_permute\b/foldr_cons_permute_strong/g
s/\bfoldr_cons_permute_eq\b/foldr_cons_permute/g
# strings
s/\bstring_rev_app\b/String.rev_app/g
s/\bstring_rev\b/String.rev/g
s/\bis_nat\b/Ascii.is_nat/g
s/\bis_space\b/Ascii.is_space/g
s/\bwords\b/String.words/g
EOF
```


## std++ 1.10.0 (2024-04-12)

The highlight of this release is the bitvector library with support for
fixed-size integers. It is distributed as a separate package,
`coq-stdpp-bitvector`. The library is developed and maintained by Michael
Sammler.

std++ 1.10 supports Coq 8.18 and 8.19.
Coq 8.16 and 8.17 are no longer supported.

This release of std++ was managed by Ralf Jung and Robbert Krebbers, with
contributions from Mathias Adam Møller, Michael Sammler, Pierre Rousselin,
Pierre Roux, and Thibaut Pérami. Thanks a lot to everyone involved!

**Detailed list of changes:**

- Add `TCSimpl` type class that is similar to `TCEq` but performs `simpl`
  before proving the goal by reflexivity.
- Add new typeclass `MThrow E M` to generally represent throwing an error of
  type `E` in monad `M`. (by Thibaut Pérami and Mathias Adam Møller)
  As a consequence:
  + Replace `MGuard` with `MThrow` and define `guard` in terms of `MThrow`.
  + The new `guard` is an ordinary function, while the old guard was a notation.
    Hence, use the monadic bind to compose guards. For example, write
    `guard P;; m`/`p ← guard P; m` instead of `guard P; m`/`guard P as p; m`.
  + Replace the tactic `case_option_guard` with a more general `case_guard`
    version.
- Equip `solve_proper` with support for subrelations. When the goal is `R x y`
  and an assumption `R' x y` is found, we search for an instance of
  `SolveProperSubrelation R' R` and if we find one, that finishes the proof.
- Remove `wf` alias for the standard `well_founded`.
- Add lemmas `Nat.lt_wf_0_projected`, `N.lt_wf_0_projected`, `Z.lt_wf_projected`
  for easy measure/size induction.
- Add `inv` tactic as a more well-behaved alternative to `inversion_clear`
  (inspired by CompCert), and `oinv` as its version on open terms.
  These tactics support both named hypotheses (`inv H`) and using a number
  to refer to a hypothesis on the goal (`inv 1`).
- Add `prod_swap : A * B → B * A` and some basic theory about it.
- Add lemma `join_app`.
- Allow patterns and type annotations in `propset` notation, e.g.,
  `{[ (x, y) : nat * nat | x = y ]}`. (by Thibaut Pérami)
- Add `inv select` and `inversion select` tactics that allow selecting the
  to-be-inverted hypothesis with a pattern.
- The new `coq-stdpp-bitvector` package contains a library for `n`-bit
  bitvectors (i.e., fixed-size integers with `n` bits).
  Users of the previous unstable version need to change the import path from
  `stdpp.unstable.bitvector` to `stdpp.bitvector.definitions` and from
  `stdpp.unstable.bitvector_tactics` to `stdpp.bitvector.tactics`. The
  complete library can be imported with `stdpp.bitvector.bitvector`.
  (by Michael Sammler)

The following `sed` script should perform most of the renaming
(on macOS, replace `sed` by `gsed`, installed via e.g. `brew install gnu-sed`).
Note that the script is not idempotent, do not run it twice.
```
sed -i -E -f- $(find theories -name "*.v") <<EOF
# well_founded
s/\bwf\b/well_founded/g
EOF
```

## std++ 1.9.0 (2023-10-11)

This highlights of this release are:
* `gmap` and related types are re-implemented based on Appel and Leroy's
  [Efficient Extensional Binary Tries](https://inria.hal.science/hal-03372247),
  making them usable in nested inductive definitions and improving
  extensionality. More information can be found in Robbert Krebbers' Coq
  Workshop talk, see https://coq-workshop.gitlab.io/2023/
* New tactics `ospecialize`, `odestruct`, `oinversion` etc are added. These
  tactics improve upon `efeed` / `edestruct` by allowing one to leave more terms
  open when specializing arguments. For instance, `odestruct (H _ x)` will turn
  the `_` into an evar rather than trying to infer it immediately, making it
  usable in many situations where `edestruct` fails. This can significantly
  shorten the overhead involved in forward reasoning proofs. For more
  information, see the test cases provided here:
  https://gitlab.mpi-sws.org/iris/stdpp/-/blob/master/tests/tactics.v#L114

std++ 1.9 supports Coq 8.16 to 8.18. Coq 8.12 to 8.15 are no longer supported.

This release of std++ was managed by Ralf Jung, Robbert Krebbers, and Johannes
Hostert, with contributions from Dorian Lesbre, Herman Bergwerf, Ike Mulder,
Isaak van Bakel, Jan-Oliver Kaiser, Jonas Kastberg, Marijn van Wezel, Michael
Sammler, Paolo Giarrusso, Tej Chajed, and Thibaut Pérami. Thanks a lot to
everyone involved!

**Detailed list of changes:**

- Rename `difference_difference` → `difference_difference_l` and
  `difference_difference_L` → `difference_difference_l_L`, add
  `difference_difference_r` and `difference_difference_r_L`.
- Let `set_solver` use `eauto` (instead of `idtac`) as its default solver.
- Add tactic `tc_solve` (this was `iSolveTC` in Iris).
- Change `f_equiv` to use `reflexivity` in a way similar to `f_equal`. That is,
  let `f_equiv` solve goals and subgoals of the form `R x x`. However, we use
  a restricted `fast_reflexivity` as full `reflexivity` can be quite expensive.
- Rename `loopup_total_empty` → `lookup_total_empty`.
- Let `naive_solver tac` fail if `tac` creates new evars. Before it would
  succeed with a proof that contains unresolved evars/shelved goals.
- Add lemmas `Nat.mul_reg_{l,r}` for cancellation of multiplication on `nat`.
  (Names are analogous to the `Z.` lemmas for Coq's standard library.)
- Rename `map_preimage` into `map_preimg` to be consistent with `dom`.
- Improve `bijective_finite`: do not require an inverse, do not unnecessarily
  remove duplicates.
- Add operation `*:` for "scalar" multiplication of multisets.
- Add `by` parameter to `multiset_solver`, which defaults to `eauto`.
- Add `map_img` operator for map image/codomain and some lemmas about it. (by
  Dorian Lesbre)
- Remove `Permutation_alt`, `submseteq_Permutation_length_le`, and
  `submseteq_Permutation_length_eq`; use `submseteq_length_Permutation` instead.
- Remove `map_to_list_length` (which seemed to be an unneeded auxiliary lemma);
  use `map_subset_size` instead.
- Rename `prefix_lookup` → `prefix_lookup_Some`.
- Extend `set_solver` with support for `set_Forall` and `set_Exists`.
- Change `lookup_union` lemma statement to use `∪` on maps instead of `union_with`.
- Add `set_omap` function for finite sets and associated lemmas. (by Dorian
  Lesbre)
- Add proof that `vec` is `Finite`. (by Herman Bergwerf.)
- Add `min` and `max` infix notations for `positive`.
- Add lemma `map_zip_fst_snd`.
- Add `stdpp.ssreflect` to provide compatibility with the ssreflect tactics.
- Set `simpl never` for `Pos` and `N` operations (similar to `Z`).
- Add `Intersection` instance for `option`. (by Marijn van Wezel)
- Add `lookup_intersection` lemma for the distributivity of lookup on an
  intersection. (by Marijn van Wezel)
- Add lemmas `map_filter_or` and `map_filter_and` for the union and intersection
  of filters on maps. (by Marijn van Wezel)
- Set `Hint Mode Equiv !`; this might need some type annotations for ambiguous
  uses of `≡`.
- Set `intuition_solver ::= auto` (the default is `auto with *`) instead of
  redeclaring `intuition`.
- Rename `option_union_Some` → `union_Some`, and strengthen it to become a
  biimplication.
- Provide new implementations of `gmap`/`gset`, `Pmap`/`Pset`, `Nmap`/`Nset` and
  `Zmap`/`Zset` based on the "canonical" version of binary tries by Appel and
  Leroy (see https://inria.hal.science/hal-03372247) that avoid the use of Sigma
  types. This has several benefits:
  + Maps enjoy more definitional equalities, because they are no longer equipped
    with a proof of canonicity. This means more equalities can be proved by
    `reflexivity` or even by conversion as part of unification. For example,
    `{[ 1 := 1; 2 := 2 ]} = {[ 2 := 2; 1 := 1 ]}` and `{[ 1 ]} ∖ {[ 1 ]} = ∅`
    hold definitionally.
  + Maps can be used in nested recursive definitions. For example,
    `Inductive gtest := GTest : gmap nat gtest → gtest`. (The old map types
    would violate Coq's strict positivity condition due to the Sigma type.)
- Make `map_fold` a primitive of the `FinMap`, and derive `map_to_list` from it.
  (`map_fold` used to be derived from `map_to_list`.) This makes it possible to
  use `map_fold` in nested-recursive definitions on maps. For example,
  `Fixpoint f (t : gtest) := let 'GTest ts := t in map_fold (λ _ t', plus (f t')) 1 ts`.
- Make `fin` number literal notations work with numbers above 10. (by Thibaut
  Pérami)
- Bind `fin` type to `fin` scope, so function taking a `fin` as argument will
  implicitly parse it in `fin` scope. (by Thibaut Pérami)
- Change premise `Equivalence` into `PreOrder` for `set_fold_proper`.
- Weaken `Proper` premises of `set_ind`, `set_fold_ind`, `set_fold_proper`. If
  you use `solve_proper` to solve these premises, no change should be needed. If
  you use a manual proof, you have to remove some `intros` and/or a `split`.
- Change `Params` of `lookup` and `lookup_total` from 4 to 5 to disable setoid
  rewriting in the key argument. If you have `Proper ((=) ==> R ==> S) lookup`,
  you should change that to `∀ k, Proper (R ==> S) (lookup k)`.
- Add lemmas for moving functions in and out of fold operations across data
  structures: new lemmas exist for sets, gmultisets, finite maps, and lists.
  (by Isaac van Bakel)
  + For the above structures, added lemmas which allow rewriting between
    `g (fold f x s)` and `fold f (g x) s` for appropriately-chosen functions
    `f`, `g` which commute.
  + For the above structures, add strong versions of the above lemmas that
    relate `g (fold f x s)` and `fold f (g x) s` by any preorder respected by
    `f`, `g` restricted to the elements of `s`.
  + Add `gmultiset_set_fold_disj_union_strong`, which generalizes
    `gmultiset_set_fold_disj_union` to any preorder for appropriately-chosen
    fold functions.
- Improve efficiency of `encode`/`decode` for `string` and `ascii`.
- Rename `equiv_Forall2` → `list_equiv_Forall2` and `equiv_option_Forall2` →
  `option_equiv_Forall2`. Add similar lemmas `list_eq_Forall2` and
  `option_eq_Forall2` for `=` instead of `≡`.
- Rename `fmap_inj` → `list_fmap_eq_inj` and `option_fmap_inj` →
  `option_fmap_eq_inj`. The new lemmas `list_fmap_inj`/`option_fmap_inj`
  generalize injectivity to `Forall2`/`option_Forall2`.
- Generalize `set_map`, `set_bind`, `set_omap`, `map_to_set` and `map_img`
  lemmas from `Set_` to `SemiSet`.
- Rename `sub_add'` to `add_sub'` for consistency with Coq's `add_sub` lemma.
- Rename `map_filter_lookup` → `map_lookup_filter` and
  `map_filter_lookup_Some` → `map_lookup_filter_Some` and
  `map_filter_lookup_None` → `map_lookup_filter_None`.
- Add `map_compose` operation, notation `m ∘ₘ n`, and associated lemmas.
  (by Dorian Lesbre)
- Add `Assoc`, `Comm`, `LeftId`, `RightId`, `LeftAbsorb`, `RightAbsorb`
  instances for number types.
- Add tactics `odestruct`, `oinversion`, `opose proof`, `ospecialize`,
  `ogeneralize` that work with open terms. All `_` remaining after inference
  will be turned into evars or subgoals using the same heuristic as `refine`.
  For instance, with `H: ∀ n, P n → Q n`, `ospecialize (H _ _)` will create an
  evar for `n` and open a subgoal for `P ?n`. `odestruct` is a more powerful
  version of `edestruct` that does not require all `_` in the destructed term to
  be immediately inferred.
- Replace `feed`/`efeed` tactics by variants of the `o` tactics that
  automatically add extra `_` until there are no more leading `∀`/`→`. `efeed
  tac` becomes `otac*`; the `feed` variants (that only specialize `→` but not
  `∀`) are no longer provided.
- Add lemmas for `reverse` of `take`/`drop` and `take`/`drop` of `reverse`.
- Rework lemmas for `take`/`drop` of an `++`:
  + Add `take_app` and `drop_app`, which are the strongest versions, and use
    `take_app_X` for derived versions.
  + Consistently use `'` suffix for version with premise `n = length`, and have
    versions without `'` with `length` inlined.
  + Rename `take_app` → `take_app_length`, `take_app_alt` → `take_app_length'`,
    `take_add_app` → `take_app_add'`, `take_app3_alt` → `take_app3_length'`,
    `drop_app` → `drop_app_length`, `drop_app_alt` → `drop_app_length'`,
    `drop_add_app` → `drop_app_add'`, `drop_app3_alt` → `drop_app3_length'`.
- Add instance `cons_equiv_inj`.

**Changes in `stdpp_unstable`:**

- Add bitvector number literal notations. (by Thibaut Pérami)

The following `sed` script should perform most of the renaming
(on macOS, replace `sed` by `gsed`, installed via e.g. `brew install gnu-sed`).
Note that the script is not idempotent, do not run it twice.
```
sed -i -E -f- $(find theories -name "*.v") <<EOF
s/\bdifference_difference(|_L)\b/difference_difference_l\1/g
s/\bloopup_total_empty\b/lookup_total_empty/g
# map_preimg
s/\bmap_preimage/map_preimg/g
s/\blookup_preimage/lookup_preimg/g
s/\blookup_total_preimage/lookup_total_preimg/g
# union_Some
s/\boption_union_Some\b/union_Some/g
# prefix_lookup
s/\bprefix_lookup\b/prefix_lookup_Some/g
# Forall2
s/\bequiv_Forall2\b/list_equiv_Forall2/g
s/\bequiv_option_Forall2\b/option_equiv_Forall2/g
s/\bfmap_inj\b/list_fmap_eq_inj/g
s/\boption_fmap_inj\b/option_fmap_eq_inj/g
# add_sub
s/\bsub_add'\b/add_sub'/g
# map filter
s/\bmap_filter_lookup/map_lookup_filter/g
# take/drop app
s/\b(take|drop)_app\b/\1_app_length/g
s/\b(take|drop)_app_alt\b/\1_app_length'/g
s/\b(take|drop)_add_app\b/\1_app_add'/g
s/\b(take|drop)_app3_alt\b/\1_app3_length'/g
EOF
```

## std++ 1.8.0 (2022-08-18)

Coq 8.16 is newly supported by this release, and Coq 8.12 to 8.15 remain
supported. Coq 8.11 is no longer supported.

This release of std++ was managed by Ralf Jung, Robbert Krebbers, and Lennard
Gäher, with contributions from Andrej Dudenhefner, Dan Frumin, Gregory Malecha,
Jan-Oliver Kaiser, Lennard Gäher, Léo Stefanesco, Michael Sammler, Paolo G. Giarrusso,
Ralf Jung, Robbert Krebbers, and Vincent Siles. Thanks a lot to everyone involved!

- Make sure that `gset` and `mapset` do not bump the universe.
- Rewrite `tele_arg` to make it not bump universes. (by Gregory Malecha, BedRock
  Systems)
- Change `dom D M` (where `D` is the domain type) to `dom M`; the domain type is
  now inferred automatically. To make this possible, getting the domain of a
  `gmap` as a `coGset` and of a `Pmap` as a `coPset` is no longer supported. Use
  `gset_to_coGset`/`Pset_to_coPset` instead.
  When combining `dom` with `≡`, this can run into an old issue (due to a Coq
  issue, `Equiv` does not the desired `Hint Mode !`), which can make it
  necessary to annotate the set type at the `≡` via `≡@{D}`.
- Rename "unsealing" lemmas from `_eq` to `_unseal`. This affects `ndot_eq` and
  `nclose_eq`. These unsealing lemmas are internal, so in principle you should
  not rely on them.
- Declare `Hint Mode` for `FinSet A C` so that `C` is input, and `A` is output
  (i.e., inferred from `C`).
- Add function `map_preimage` to compute the preimage of a finite map.
- Rename `map_disjoint_subseteq` → `kmap_subseteq` and
  `map_disjoint_subset` → `kmap_subset`.
- Add `map_Exists` as an analogue to `map_Forall`. (by Michael Sammler)
- Add `case_match eqn:H` that behaves like `case_match` but allows naming the
  generated equality. (by Michael Sammler)
- Flip direction of `map_disjoint_fmap`.
- Add `map_agree` as a weaker version of `##ₘ` which requires the maps to agree
  on keys contained in both maps. (by Michael Sammler)
- Rename `lookup_union_l` → `lookup_union_l'` and add `lookup_union_l`
  as the dual to `lookup_union_r`.
- Add `map_seqZ` as the `Z` analogue of `map_seq`. (by Michael Sammler)
- Add the `coq-stdpp-unstable` package for libraries that are not
  deemed stable enough to be included in the main std++ library,
  following the `coq-iris-unstable` package. This library is contained
  in the `stdpp_unstable` folder. The `theories` folder was renamed
  to `stdpp`.
- Add an unstable `bitblast` tactic for solving equalities between integers
  involving bitwise operations. (by Michael Sammler)
- Add the bind operation `set_bind` for finite sets. (by Dan Frumin and Paolo G.
  Giarrusso)
- Change `list_fmap_ext` and `list_fmap_equiv_ext` to require equality on the
  elements of the list, not on all elements of the carrier type. This change
  makes these lemmas consistent with those for maps.
- Use the modules `Nat`, `Pos`, `N`, `Z`, `Nat2Z`, `Z2Nat`, `Nat2N`, `Pos2Nat`,
  `SuccNat2Pos`, and `N2Z` for our extended results on number types. Before,
  we prefixed our the std++ lemmas with `Nat_` or `nat_`, but now you refer
  to them with `Nat.`, similar to the way you refer to number lemmas from Coq's
  standard library.
- Use a module `Qp` for our positive rationals library. You now refer to `Qp`
  lemmas using `Qp.lem` instead of `Qp_lem`.
- Rename `_plus`/`_minus` into `_add`/`_sub` to be consistent with Coq's current
  convention for numbers. See the sed script below for an exact list of renames.
- Refactor the `feed` and `efeed` tactics. In particular, improve the
  documentation of `(e)feed` tactics, rename the primitive `(e)feed`
  tactic to `(e)feed_core`, make the syntax of `feed_core` consistent
  with `efeed_core`, remove the `by` parameter of `efeed_core`, and add
  `(e)feed generalize`, `efeed inversion`, and `efeed destruct`.

The following `sed` script should perform most of the renaming
(on macOS, replace `sed` by `gsed`, installed via e.g. `brew install gnu-sed`).
Note that the script is not idempotent, do not run it twice.
```
sed -i -E -f- $(find theories -name "*.v") <<EOF
s/\bmap_disjoint_subseteq\b/kmap_subseteq/g
s/\bmap_disjoint_subset\b/kmap_subset/g
s/\blookup_union_l\b/lookup_union_l'/g
# number modules --- note that this might rename your own lemmas
# start with Nat_/N_/Z_/Qp_/P(app|reverse|length|dup)_ too eagerly.
# Also the list of names starting with nat_ is not complete.
s/\bNat_/Nat\./g
s/\bNat.iter_S(|_r)\b/Nat.iter_succ\1/g
s/\bP(app|reverse|length|dup)/Pos\.\1/g
s/\bPlt_sum\b/Pos\.lt_sum/g
s/\bPos\.reverse_Pdup\b/Pos\.reverse_Pdup/g
s/\bnat_(le_sum|eq_dec|lt_pi)\b/Nat\.\1/g
s/\bN_/N\./g
s/\bZ_/Z\./g
s/\bZ\.scope\b/Z_scope/g
s/\bN\.scope\b/N_scope/g
s/\Z\.of_nat_complete\b/Z_of_nat_complete/g
s/\bZ\.of_nat_inj\b/Nat2Z.inj/g
s/\bZ2Nat_/Z2Nat\./g
s/\bNat2Z_/Nat2Z\./g
s/\bQp_/Qp\./g
s/\bQp\.1_1/Qp\.add_1_1/g
# plus → add
s/\bfin_plus_inv\b/fin_add_inv/g
s/\bfin_plus_inv_L\b/fin_add_inv_l/g
s/\bfin_plus_inv_R\b/fin_add_inv_r/g
s/\bset_seq_plus\b/set_seq_add/g
s/\bset_seq_plus_L\b/set_seq_add_L/g
s/\bset_seq_plus_disjoint\b/set_seq_add_disjoint/g
s/\bnsteps_plus_inv\b/nsteps_add_inv/g
s/\bbsteps_plus_r\b/bsteps_add_r/g
s/\bbsteps_plus_l\b/bsteps_add_l/g
s/\btake_plus_app\b/take_add_app/g
s/\breplicate_plus\b/replicate_add/g
s/\btake_replicate_plus\b/take_replicate_add/g
s/\bdrop_replicate_plus\b/drop_replicate_add/g
s/\bresize_plus\b/resize_add/g
s/\bresize_plus_eq\b/resize_add_eq/g
s/\btake_resize_plus\b/take_resize_add/g
s/\bdrop_resize_plus\b/drop_resize_add/g
s/\bdrop_plus_app\b/drop_add_app/g
s/\bMakeNatPlus\b/MakeNatAdd/g
s/\bmake_nat_plus\b/make_nat_add/g
s/\bnat_minus_plus\b/Nat\.sub_add/g
s/\bnat_le_plus_minus\b/Nat\.le_add_sub/g
EOF
```

## std++ 1.7.0 (2022-01-22)

Coq 8.15 is newly supported by this release, and Coq 8.11 to 8.14 remain
supported. Coq 8.10 is no longer supported.

This release of std++ was managed by Ralf Jung, Robbert Krebbers, and Tej
Chajed, with contributions from Glen Mével, Jonas Kastberg Hinrichsen, Matthieu
Sozeau, Michael Sammler, Ralf Jung, Robbert Krebbers, and Tej Chajed. Thanks a
lot to everyone involved!

- Add `is_closed_term` tactic for determining whether a term depends on variables bound
  in the context. (by Michael Sammler)
- Add `list.zip_with_take_both` and `list.zip_with_take_both'`
- Specialize `list.zip_with_take_{l,r}`, add generalized lemmas `list.zip_with_take_{l,r}'`
- Add `bool_to_Z` that converts true to 1 and false to 0. (by Michael Sammler)
- Add lemmas for lookup on `mjoin` for lists. (by Michael Sammler)
- Rename `Is_true_false` → `Is_true_false_2` and `eq_None_ne_Some` → `eq_None_ne_Some_1`.
- Rename `decide_iff` → `decide_ext` and `bool_decide_iff` → `bool_decide_ext`.
- Remove a spurious `Global Arguments Pos.of_nat : simpl never`.
- Add tactics `destruct select <pat>` and `destruct select <pat> as <intro_pat>`.
- Add some more lemmas about `Finite` and `pred_finite`.
- Add lemmas about `last`: `last_app_cons`, `last_app`, `last_Some`, and
  `last_Some_elem_of`.
- Add versions of Pigeonhole principle for Finite types, natural numbers, and
  lists.

The following `sed` script should perform most of the renaming
(on macOS, replace `sed` by `gsed`, installed via e.g. `brew install gnu-sed`).
Note that the script is not idempotent, do not run it twice.
```
sed -i -E -f- $(find theories -name "*.v") <<EOF
s/\bIs_true_false\b/Is_true_false_2/g
s/\beq_None_ne_Some\b/eq_None_ne_Some_1/g
# bool decide
s/\b(bool_|)decide_iff\b/\1decide_ext/g
EOF
```

## std++ 1.6.0 (2021-11-05)

Coq 8.14 is newly supported by this release, and Coq 8.10 to 8.13 remain
supported.

This release of std++ was managed by Ralf Jung, Robbert Krebbers, and Tej
Chajed, with contributions from Alix Trieu, Andrej Dudenhefner, Dan Frumin,
Fengmin Zhu, Hoang-Hai Dang, Jan Menz, Lennard Gäher, Michael Sammler, Paolo G.
Giarrusso, Ralf Jung, Robbert Krebbers, Simon Friis Vindum, Simon Gregersen, and
Tej Chajed. Thanks a lot to everyone involved!

- Remove singleton notations `{[ x,y ]}` and `{[ x,y,z ]}` for `{[ (x,y) ]}`
  and `{[ (x,y,z) ]}`. They date back to the time we used the `singleton` class
  with a product for maps (there's now the `singletonM` class).
- Add map notations `{[ k1 := x1 ; .. ; kn := xn ]}` up to arity 13.
  (by Lennard Gäher)
- Add multiset literal notation `{[+ x1; .. ; xn +]}`.
  + Add a new type class `SingletonMS` (with projection `{[+ x +]}` for
    multiset singletons.
  + Define `{[+ x1; .. ; xn +]}` as notation for `{[+ x1 +]} ⊎ .. ⊎ {[+ xn +]}`.
- Remove the `Singleton` and `Semiset` instances for multisets to avoid
  accidental use.
  + This means the notation `{[ x1; .. ; xn ]}` no longer works for multisets
    (previously, its definition was wrong, since it used `∪` instead of `⊎`).
  + Add lemmas for `∈` and `∉` specific for multisets, since the set lemmas no
    longer work for multisets.
- Make `Qc_of_Z'` not an implicit coercion (from `Z` to `Qc`) any more.
- Make `Z.of_nat'` not an implicit coercion (from `nat` to `Z`) any more.
- Rename `decide_left` → `decide_True_pi` and `decide_right` → `decide_False_pi`.
- Add `option_guard_True_pi`.
- Add lemma `surjective_finite`. (by Alix Trieu)
- Add type classes `TCFalse`, `TCUnless`, `TCExists`, and `TCFastDone`. (by
  Michael Sammler)
- Add various results about bit representations of `Z`. (by Michael Sammler)
- Add tactic `learn_hyp`. (by Michael Sammler)
- Add `Countable` instance for decidable Sigma types. (by Simon Gregersen)
- Add tactics `compute_done` and `compute_by` for solving goals by computation.
- Add `Inj` instances for `fmap` on option and maps.
- Various changes to `Permutation` lemmas:
  + Rename `Permutation_nil` → `Permutation_nil_r`,
    `Permutation_singleton` → `Permutation_singleton_r`, and
    `Permutation_cons_inv` → `Permutation_cons_inv_r`.
  + Add lemmas `Permutation_nil_l`, `Permutation_singleton_l`, and
    `Permutation_cons_inv_l`.
  + Add new instance `cons_Permutation_inj_l : Inj (=) (≡ₚ) (.:: k).`.
  + Add lemma `Permutation_cross_split`.
  + Make lemma `elem_of_Permutation` a biimplication
- Add function `kmap` to transform the keys of finite maps.
- Set `Hint Mode` for the classes `PartialOrder`, `TotalOrder`, `MRet`, `MBind`,
  `MJoin`, `FMap`, `OMap`, `MGuard`, `SemiSet`, `Set_`, `TopSet`, and `Infinite`.
- Strengthen the extensionality lemmas `map_filter_ext` and
  `map_filter_strong_ext`:
  + Rename `map_filter_strong_ext` → `map_filter_strong_ext_1` and
    `map_filter_ext` → `map_filter_ext_1`.
  + Add new bidirectional lemmas `map_filter_strong_ext` and `map_filter_ext`.
  + Add `map_filter_strong_ext_2` and `map_filter_ext_2`.
- Make collection of lemmas for filter + union/disjoint consistent for sets and
  maps:
  + Sets: Add lemmas `disjoint_filter`, `disjoint_filter_complement`, and
    `filter_union_complement`.
  + Maps: Rename `map_disjoint_filter` → `map_disjoint_filter_complement` and
    `map_union_filter` → `map_filter_union_complement` to be consistent with sets.
  + Maps: Add lemmas `map_disjoint_filter` and `map_filter_union` analogous to
    sets.
- Add cross split lemma `map_cross_split` for maps
- Setoid results for options:
  + Add instance `option_fmap_equiv_inj`.
  + Add `Proper` instances for `union`, `union_with`, `intersection_with`, and
    `difference_with`.
  + Rename instances `option_mbind_proper` → `option_bind_proper` and
    `option_mjoin_proper` → `option_join_proper` to be consistent with similar
    instances for sets and lists.
  + Rename `equiv_None` → `None_equiv_eq`.
  + Replace `equiv_Some_inv_l`, `equiv_Some_inv_r`, `equiv_Some_inv_l'`, and
    `equiv_Some_inv_r'` by new lemma `Some_equiv_eq` that follows the pattern of
    other `≡`-inversion lemmas: it uses a `↔` and puts the arguments of `≡` and
    `=` in consistent order.
- Setoid results for lists:
  + Add `≡`-inversion lemmas `nil_equiv_eq`, `cons_equiv_eq`,
    `list_singleton_equiv_eq`,  and `app_equiv_eq`.
  + Add lemmas `Permutation_equiv` and `equiv_Permutation`.
- Setoid results for maps:
  + Add instances `map_singleton_equiv_inj` and `map_fmap_equiv_inj`.
  + Add and generalize many `Proper` instances.
  + Add lemma `map_equiv_lookup_r`.
  + Add lemma `map_equiv_iff`.
  + Rename `map_equiv_empty` → `map_empty_equiv_eq`.
  + Add `≡`-inversion lemmas `insert_equiv_eq`, `delete_equiv_eq`,
    `map_union_equiv_eq`, etc.
- Drop `DiagNone` precondition of `lookup_merge` rule of `FinMap` interface.
  + Drop `DiagNone` class.
  + Add `merge_proper` instance.
  + Simplify lemmas about `merge` by dropping the `DiagNone` precondition.
  + Generalize lemmas `partial_alter_merge`, `partial_alter_merge_l`, and
    `partial_alter_merge_r`.
  + Drop unused `merge_assoc'` instance.
- Improvements to `head` and `tail` functions for lists:
  + Define `head` as notation that prints (Coq defines it as `parsing only`)
    similar to `tail`.
  + Declare `tail` as `simpl nomatch`.
  + Add lemmas about `head` and `tail`.
- Add and extend equivalences between closure operators:
  - Add `↔` lemmas that relate `rtc`, `tc`, `nsteps`, and `bsteps`.
  - Rename `→` lemmas `rtc_nsteps` → `rtc_nsteps_1`,
    `nsteps_rtc` → `rtc_nsteps_2`, `rtc_bsteps` → `rtc_bsteps_1`, and
    `bsteps_rtc` → `rtc_bsteps_2`.
  - Add lemmas that relate `rtc`, `tc`, `nsteps`, and `bsteps` to path
    representations as lists.
- Remove explicit equality from cross split lemmas so that they become easier
  to use in forward-style proofs.
- Add lemmas for finite maps: `dom_map_zip_with`, `dom_map_zip_with_L`,
  `map_filter_id`, `map_filter_subseteq`, and `map_lookup_zip_Some`.
- Add lemmas for sets: `elem_of_weaken` and `not_elem_of_weaken`.
- Rename `insert_delete` → `insert_delete_insert`; add new `insert_delete` that
  is consistent with `delete_insert`.
- Fix statement of `sum_inhabited_r`. (by Paolo G. Giarrusso)
- Make `done` work on goals of the form `is_Some`.
- Add `mk_evar` tactic to generate evars (intended as a more useful replacement
  for Coq's `evar` tactic).
- Make `solve_ndisj` able to solve more goals of the form `_ ⊆ ⊤ ∖ _`,
  `_ ∖ _ ## _`, `_ ## _ ∖ _`, as well as `_ ## ∅` and `∅ ## _`,
  and goals containing `_ ∖ _ ∖ _`.
- Improvements to curry:
  + Swap names of `curry`/`uncurry`, `curry3`/`uncurry3`, `curry4`/`uncurry4`,
    `gmap_curry`/`gmap_uncurry`, and `hcurry`/`huncurry` to be consistent with
    Haskell and friends.
  + Add `Params` and `Proper` instances for `curry`/`uncurry`,
    `curry3`/`uncurry3`, and `curry4`/`uncurry4`.
  + Add lemmas that say that `curry`/`curry3`/`curry4` and
    `uncurry`/`uncurry3`/`uncurry4` are inverses.
- Rename `map_union_subseteq_l_alt` → `map_union_subseteq_l'` and
  `map_union_subseteq_r_alt` → `map_union_subseteq_r'` to be consistent with
  `or_intro_{l,r}'`.
- Add `union_subseteq_l'`, `union_subseteq_r'` as transitive versions of
  `union_subseteq_l`, `union_subseteq_r` that can be more easily `apply`ed.
- Rename `gmultiset_elem_of_singleton_subseteq` → `gmultiset_singleton_subseteq_l`
  and swap the equivalence to be consistent with Iris's `singleton_included_l`. Add
  `gmultiset_singleton_subseteq`, which is similar to `singleton_included` in
  Iris.
- Add lemmas `singleton_subseteq_l` and `singleton_subseteq` for sets.
- Add lemmas `map_singleton_subseteq_l` and `map_singleton_subseteq` for maps.
- Add lemmas `singleton_submseteq_l` and `singleton_submseteq` for unordered
  list inclusion, as well as `lookup_submseteq` and `submseteq_insert`.
- Make `map_empty` a biimplication.
- Clean up `empty{',_inv,_iff}` lemmas:
  + Write them all using `↔` and consistently use the `_iff` suffix.
    (But keep the `_inv` version when it is useful for rewriting.)
  + Remove `map_to_list_empty_inv_alt`; chain `Permutation_nil_r` and
    `map_to_list_empty_iff` instead.
  + Add lemma `map_filter_empty_iff`.
- Add generalized lemma `map_filter_insert` that covers both the True and False
  case. Rename old `map_filter_insert` → `map_filter_insert_True` and
  `map_filter_insert_not_delete` → `map_filter_insert_False`.
- Weaken premise of `map_filter_delete_not` to make it consistent with
  `map_filter_insert_not'`.
- Add lemmas for maps: `map_filter_strong_subseteq_ext`, `map_filter_subseteq_ext`,
  `map_filter_subseteq_mono`, `map_filter_singleton`, `map_filter_singleton_True`,
  `map_filter_singleton_False`, `map_filter_comm`, `map_union_least`,
  `map_subseteq_difference_l`, `insert_difference`, `insert_difference'`,
  `difference_insert`, `difference_insert_subseteq`. (by Hai Dang)
- Add `map_size_disj_union`, `size_dom`, `size_list_to_set`.
- Tweak reduction on `gset`, so that `cbn` matches the behavior by `simpl` and
  does not unfold `gset` operations. (by Paolo G. Giarrusso, BedRock Systems)
- Add `get_head` tactic to determine the syntactic head of a function
  application term.
- Add map lookup lemmas: `lookup_union_is_Some`, `lookup_difference_is_Some`,
  `lookup_union_Some_l_inv`, `lookup_union_Some_r_inv`.
- Make `Forall2_nil`, `Forall2_cons` bidirectional lemmas with `Forall2_nil_2`,
  `Forall2_cons_2` being the original one-directional versions (matching
  `Forall_nil` and `Forall_cons`). Rename `Forall2_cons_inv` to `Forall2_cons_1`.
- Enable `f_equiv` (and by extension `solve_proper`) to handle goals of the form
  `f x ≡ g x` when `f ≡ g` is in scope, where `f` has a type like Iris's `-d>`
  and `-n>`.
- Optimize `f_equiv` by doing more syntactic checking before handing off to
  unification. This can make some uses 50x faster, but also makes the tactic
  slightly weaker in case the left-hand side and right-hand side of the relation
  call a function with arguments that are convertible but not syntactically
  equal.
- Add lemma `choose_proper` showing that `choose P` respects predicate
  equivalence. (by Paolo G. Giarrusso, BedRock Systems)
- Extract module `well_founded` from `relations`, and re-export it for
  compatibility. This contains `wf`, `Acc_impl`, `wf_guard`,
  `wf_projected`, `Fix_F_proper`, `Fix_unfold_rel`.
- Add induction principle `well_founded.Acc_dep_ind`, a dependent
  version of `Acc_ind`. (by Paolo G. Giarrusso, BedRock Systems)

The following `sed` script should perform most of the renaming
(on macOS, replace `sed` by `gsed`, installed via e.g. `brew install gnu-sed`).
Note that the script is not idempotent, do not run it twice.
```
sed -i -E -f- $(find theories -name "*.v") <<EOF
s/\bdecide_left\b/decide_True_pi/g
s/\bdecide_right\b/decide_False_pi/g
# Permutation
s/\bPermutation_nil\b/Permutation_nil_r/g
s/\bPermutation_singleton\b/Permutation_singleton_r/g
s/\Permutation_cons_inv\b/Permutation_cons_inv_r/g
# Filter
s/\bmap_disjoint_filter\b/map_disjoint_filter_complement/g
s/\bmap_union_filter\b/map_filter_union_complement/g
# mbind
s/\boption_mbind_proper\b/option_bind_proper/g
s/\boption_mjoin_proper\b/option_join_proper/g
# relations
s/\brtc_nsteps\b/rtc_nsteps_1/g
s/\bnsteps_rtc\b/rtc_nsteps_2/g
s/\brtc_bsteps\b/rtc_bsteps_1/g
s/\bbsteps_rtc\b/rtc_bsteps_2/g
# setoid
s/\bequiv_None\b/None_equiv_eq/g
s/\bmap_equiv_empty\b/map_empty_equiv_eq/g
# insert_delete
s/\binsert_delete\b/insert_delete_insert/g
# filter extensionality lemmas
s/\bmap_filter_ext\b/map_filter_ext_1/g
s/\bmap_filter_strong_ext\b/map_filter_strong_ext_1/g
# swap curry/uncurry
s/\b(lookup_gmap_|gmap_|h|)curry(|3|4)\b/OLD\1curry\2/g
s/\b(lookup_gmap_|gmap_|h|)uncurry(|3|4)\b/\1curry\2/g
s/\bOLD(lookup_gmap_|gmap_|h|)curry(|3|4)\b/\1uncurry\2/g
s/\bgmap_curry_uncurry\b/gmap_uncurry_curry/g
s/\bgmap_uncurry_non_empty\b/gmap_curry_non_empty/g
s/\bgmap_uncurry_curry_non_empty\b/gmap_curry_uncurry_non_empty/g
s/\bhcurry_uncurry\b/huncurry_curry/g
s/\blookup_gmap_uncurry_None\b/lookup_gmap_curry_None/g
# map_union_subseteq
s/\bmap_union_subseteq_(r|l)_alt\b/map_union_subseteq_\1'/g
# singleton
s/\bgmultiset_elem_of_singleton_subseteq\b/gmultiset_singleton_subseteq_l/g
# empty_iff
s/\bmap_to_list_empty('|_inv)\b/map_to_list_empty_iff/g
s/\bkmap_empty_inv\b/kmap_empty_iff/g
s/\belements_empty'\b/elements_empty_iff/g
s/\bgmultiset_elements_empty'\b/gmultiset_elements_empty_iff/g
# map_filter_insert
s/\bmap_filter_insert\b/map_filter_insert_True/g
s/\bmap_filter_insert_not_delete\b/map_filter_insert_False/g
# Forall2
s/\bForall2_cons_inv\b/Forall2_cons_1/g
EOF
```

## std++ 1.5.0 (2021-02-16)

Coq 8.13 is newly supported by this release, Coq 8.8 and 8.9 are no longer
supported.

This release of std++ was managed by Ralf Jung and Robbert Krebbers, with
contributions by Alix Trieu, Dan Frumin, Hugo Herbelin, Paulo Emílio de Vilhena,
Simon Friis Vindum, and Tej Chajed.  Thanks a lot to everyone involved!

- Overhaul of the theory of positive rationals `Qp`:
  + Add `max` and `min` operations for `Qp`.
  + Add the orders `Qp_le` and `Qp_lt`.
  + Rename `Qp_plus` into `Qp_add` and `Qp_mult` into `Qp_mul` to be consistent
    with the corresponding names for `nat`, `N`, and `Z`.
  + Add a function `Qp_inv` for the multiplicative inverse.
  + Define the division function `Qp_div` in terms of `Qp_inv`, and generalize
    the second argument from `positive` to `Qp`.
  + Add a function `pos_to_Qp` that converts a `positive` into a positive
    rational `Qp`.
  + Add many lemmas and missing type class instances, especially for orders,
    multiplication, multiplicative inverse, division, and the conversion.
  + Remove the coercion from `Qp` to `Qc`. This follows our recent tradition of
    getting rid of coercions since they are more often confusing than useful.
  + Rename the conversion from `Qp_car : Qp → Qc` into `Qp_to_Qc` to be
    consistent with other conversion functions in std++. Also rename the lemma
    `Qp_eq` into `Qp_to_Qc_inj_iff`.
  + Use `let '(..) = ...` in the definitions of `Qp_plus`, `Qp_mult`, `Qp_inv`,
    `Qp_le` and `Qp_lt` to avoid Coq tactics (like `injection`) to unfold these
    definitions eagerly.
  + Define the `Qp` literals 1, 2, 3, 4 in terms of `pos_to_Qp` instead of
    iterated addition.
  + Rename and restate many lemmas so as to be consistent with the conventions
    for Coq's number types `nat`, `N`, and `Z`.
- Add `rename select <pat> into <name>` tactic to find a hypothesis by pattern
  and give it a fixed name.
- Add `eunify` tactic that lifts Coq's `unify` tactic to `open_constr`.
- Generalize `omap_insert`, `omap_singleton`, `map_size_insert`, and
  `map_size_delete` to cover the `Some` and `None` case. Add `_Some` and `_None`
  versions of the lemmas for the specific cases.
- Rename `dom_map filter` → `dom_filter`, `dom_map_filter_L` → `dom_filter_L`,
  and `dom_map_filter_subseteq` → `dom_filter_subseteq` for consistency's sake.
- Remove unused notations `∪**`, `∪*∪**`, `∖**`, `∖*∖**`, `⊆**`, `⊆1*`, `⊆2*`,
  `⊆1**`, `⊆2**"`, `##**`, `##1*`, `##2*`, `##1**`, `##2**` for nested
  `zip_with` and `Forall2` versions of `∪`, `∖`, and `##`.
- Remove unused type classes `DisjointE`, `DisjointList`, `LookupE`, and
  `InsertE`.
- Fix a bug where `pretty 0` was defined as `""`, the empty string. It now
  returns `"0"` for `N`, `Z`, and `nat`.
- Remove duplicate `map_fmap_empty` of `fmap_empty`, and rename
  `map_fmap_empty_inv` into `fmap_empty_inv` for consistency's sake.
- Rename `seq_S_end_app` to `seq_S`. (The lemma `seq_S` is also in Coq's stdlib
  since Coq 8.12.)
- Remove `omega` import and hint database in `tactics` file.
- Remove unused `find_pat` tactic that was made mostly obsolete by `select`.
- Rename `_11` and `_12` into `_1_1` and `_1_2`, respectively. These suffixes
  are used for `A → B1` and `A → B2` variants of `A ↔ B1 ∧ B2` lemmas.
- Rename `Forall_Forall2` → `Forall_Forall2_diag` to be consistent with the
  names for big operators in Iris.
- Rename set equality and equivalence lemmas:
  `elem_of_equiv_L` → `set_eq`,
  `set_equiv_spec_L` → `set_eq_subseteq`,
  `elem_of_equiv` → `set_equiv`,
  `set_equiv_spec` → `set_equiv_subseteq`.
- Remove lemmas `map_filter_iff` and `map_filter_lookup_eq` in favor of the stronger
  extensionality lemmas `map_filter_ext` and `map_filter_strong_ext`.

The following `sed` script should perform most of the renaming
(on macOS, replace `sed` by `gsed`, installed via e.g. `brew install gnu-sed`):
```
sed -i -E '
s/\bQp_plus\b/Qp_add/g
s/\bQp_mult\b/Qp_mul/g
s/\bQp_mult_1_l\b/Qp_mul_1_l/g
s/\bQp_mult_1_r\b/Qp_mul_1_r/g
s/\bQp_plus_id_free\b/Qp_add_id_free/g
s/\bQp_not_plus_ge\b/Qp_not_add_le_l/g
s/\bQp_le_plus_l\b/Qp_le_add_l/g
s/\bQp_mult_plus_distr_l\b/Qp_mul_add_distr_r/g
s/\bQp_mult_plus_distr_r\b/Qp_mul_add_distr_l/g
s/\bmap_fmap_empty\b/fmap_empty/g
s/\bmap_fmap_empty_inv\b/fmap_empty_inv/g
s/\bseq_S_end_app\b/seq_S/g
s/\bomap_insert\b/omap_insert_Some/g
s/\bomap_singleton\b/omap_singleton_Some/g
s/\bomap_size_insert\b/map_size_insert_None/g
s/\bomap_size_delete\b/map_size_delete_Some/g
s/\bNoDup_cons_11\b/NoDup_cons_1_1/g
s/\bNoDup_cons_12\b/NoDup_cons_1_2/g
s/\bmap_filter_lookup_Some_11\b/map_filter_lookup_Some_1_1/g
s/\bmap_filter_lookup_Some_12\b/map_filter_lookup_Some_1_2/g
s/\bmap_Forall_insert_11\b/map_Forall_insert_1_1/g
s/\bmap_Forall_insert_12\b/map_Forall_insert_1_2/g
s/\bmap_Forall_union_11\b/map_Forall_union_1_1/g
s/\bmap_Forall_union_12\b/map_Forall_union_1_2/g
s/\bForall_Forall2\b/Forall_Forall2_diag/g
s/\belem_of_equiv_L\b/set_eq/g
s/\bset_equiv_spec_L\b/set_eq_subseteq/g
s/\belem_of_equiv\b/set_equiv/g
s/\bset_equiv_spec\b/set_equiv_subseteq/g
' $(find theories -name "*.v")
```

## std++ 1.4.0 (released 2020-07-15)

Coq 8.12 is newly supported by this release, and Coq 8.7 is no longer supported.

This release of std++ received contributions by Gregory Malecha, Michael
Sammler, Olivier Laurent, Paolo G. Giarrusso, Ralf Jung, Robbert Krebbers,
sarahzrf, and Tej Chajed.

- Rename `Z2Nat_inj_div` and `Z2Nat_inj_mod` to `Nat2Z_inj_div` and
  `Nat2Z_inj_mod` to follow the naming convention of `Nat2Z` and
  `Z2Nat`. Re-purpose the names `Z2Nat_inj_div` and `Z2Nat_inj_mod` for be the
  lemmas they should actually be.
- Add `rotate` and `rotate_take` functions for accessing a list with
  wrap-around. Also add `rotate_nat_add` and `rotate_nat_sub` for
  computing indicies into a rotated list.
- Add the `select` and `revert select` tactics for selecting and
  reverting a hypothesis based on a pattern.
- Extract `list_numbers.v` from `list.v` and `numbers.v` for
  functions, which operate on lists of numbers (`seq`, `seqZ`,
  `sum_list(_with)` and `max_list(_with)`). `list_numbers.v` is
  exported by the prelude. This is a breaking change if one only
  imports `list.v`, but not the prelude.
- Rename `drop_insert` into `drop_insert_gt` and add `drop_insert_le`.
- Add `Countable` instance for `Ascii.ascii`.
- Make lemma `list_find_Some` more apply friendly.
- Add `filter_app` lemma.
- Add tactic `multiset_solver` for solving goals involving multisets.
- Rename `fin_maps.singleton_proper` into `singletonM_proper` since it concerns
  `singletonM` and to avoid overlap with `sets.singleton_proper`.
- Add `wn R` for weakly normalizing elements w.r.t. a relation `R`.
- Add `encode_Z`/`decode_Z` functions to encode elements of a countable type
  as integers `Z`, in analogy with `encode_nat`/`decode_nat`.
- Fix list `Datatypes.length` and string `strings.length` shadowing (`length`
  should now always be `Datatypes.length`).
- Change the notation for pattern matching monadic bind into `'pat ← x; y`. It
  was `''pat ← x; y` (with double `'`) due to a shortcoming of Coq ≤8.7.

## std++ 1.3.0 (released 2020-03-18)

Coq 8.11 is supported by this release.

This release of std++ received contributions by Amin Timany, Armaël Guéneau,
Dan Frumin, David Swasey, Jacques-Henri Jourdan, Michael Sammler, Paolo G.
Giarrusso, Pierre-Marie Pédrot, Ralf Jung, Robbert Krebbers, Simon Friis Vindum,
Tej Chajed, and William Mansky

Noteworthy additions and changes:

- Rename `dom_map_filter` into `dom_map_filter_subseteq` and repurpose
  `dom_map_filter` for the version with the equality. This follows the naming
  convention for similar lemmas.
- Generalize `list_find_Some` and `list_find_None` to become bi-implications.
- Disambiguate Haskell-style notations for partially applied operators. For
  example, change `(!! i)` into `(.!! x)` so that `!!` can also be used as a
  prefix, as done in VST. A sed script to perform the renaming can be found at:
  https://gitlab.mpi-sws.org/iris/stdpp/merge_requests/93
- Add type class `TopSet` for sets with a `⊤` element. Provide instances for
  `boolset`, `propset`, and `coPset`.
- Add `set_solver` support for `dom`.
- Rename `vec_to_list_of_list` into `vec_to_list_to_vec`, and add new lemma
  `list_to_vec_to_list` for the converse.
- Rename `fin_of_nat` into `nat_to_fin`, `fin_to_of_nat` into
  `fin_to_nat_to_fin`, and `fin_of_to_nat` into `nat_to_fin_to_nat`, to follow
  the conventions.
- Add `Countable` instance for `vec`.
- Introduce `destruct_or{?,!}` to repeatedly destruct disjunctions in
  assumptions. The tactic can also be provided an explicit assumption name;
  `destruct_and{?,!}` has been generalized accordingly and now can also be
  provided an explicit assumption name.
  Slight breaking change: `destruct_and` no longer handle `False`;
  `destruct_or` now handles `False` while `destruct_and` handles `True`,
  as the respective units of disjunction and conjunction.
- Add tactic `set_unfold in H`.
- Set `Hint Mode` for `TCAnd`, `TCOr`, `TCForall`, `TCForall2`, `TCElemOf`,
  `TCEq`, and `TCDiag`.
- Add type class `LookupTotal` with total lookup operation `(!!!) : M → K → A`.
  Provide instances for `list`, `fin_map`, and `vec`, as well as corresponding
  lemmas for the operations on these types. The instance for `vec` replaces the
  ad-hoc `!!!` definition. As a consequence, arguments of `!!!` are no longer
  parsed in `vec_scope` and `fin_scope`, respectively. Moreover, since `!!!`
  is overloaded, coercions around `!!!` no longer work.
- Make lemmas for `seq` and `seqZ` consistent:
  + Rename `fmap_seq` → `fmap_S_seq`
  + Add `fmap_add_seq`, and rename `seqZ_fmap` → `fmap_add_seqZ`
  + Rename `lookup_seq` → `lookup_seq_lt`
  + Rename `seqZ_lookup_lt` → `lookup_seqZ_lt`,
    `seqZ_lookup_ge` → `lookup_seqZ_ge`, and `seqZ_lookup` → `lookup_seqZ`
  + Rename `lookup_seq_inv` → `lookup_seq` and generalize it to a bi-implication
  + Add `NoDup_seqZ` and `Forall_seqZ`

The following `sed` script should perform most of the renaming
(on macOS, replace `sed` by `gsed`, installed via e.g. `brew install gnu-sed`):
```
sed -i '
s/\bdom_map_filter\b/dom_map_filter_subseteq/g
s/\bfmap_seq\b/fmap_S_seq/g
s/\bseqZ_fmap\b/fmap_add_seqZ/g
s/\blookup_seq\b/lookup_seq_lt/g
s/\blookup_seq_inv\b/lookup_seq/g
s/\bseqZ_lookup_lt\b/lookup_seqZ_lt/g
s/\bseqZ_lookup_ge\b/lookup_seqZ_ge/g
s/\bseqZ_lookup\b/lookup_seqZ/g
s/\bvec_to_list_of_list\b/vec_to_list_to_vec/g
s/\bfin_of_nat\b/nat_to_fin/g
s/\bfin_to_of_nat\b/fin_to_nat_to_fin/g
s/\bfin_of_to_nat\b/nat_to_fin_to_nat/g
' $(find theories -name "*.v")
```

## std++ 1.2.1 (released 2019-08-29)

This release of std++ received contributions by Dan Frumin, Michael Sammler,
Paolo G. Giarrusso, Paulo Emílio de Vilhena, Ralf Jung, Robbert Krebbers,
Rodolphe Lepigre, and Simon Spies.

Noteworthy additions and changes:

- Introduce `max` and `min` infix notations for `N` and `Z` like we have for `nat`.
- Make `solve_ndisj` tactic more powerful.
- Add type class `Involutive`.
- Improve `naive_solver` performance in case the goal is trivially solvable.
- Add a bunch of new lemmas for list, set, and map operations.
- Rename `lookup_imap` into `map_lookup_imap`.

## std++ 1.2.0 (released 2019-04-26)

Coq 8.9 is supported by this release, but Coq 8.6 is no longer supported. Use
std++ 1.1 if you have to use Coq 8.6. The repository moved to a new location at
https://gitlab.mpi-sws.org/iris/stdpp and automatically generated Coq-doc of
master is available at https://plv.mpi-sws.org/coqdoc/stdpp/.

This release of std++ received contributions by Dan Frumin, Hai Dang, Jan-Oliver
Kaiser, Mackie Loeffel, Maxime Dénès, Ralf Jung, Robbert Krebbers, and Tej
Chajed.

New features:

- New notations `=@{A}`, `≡@{A}`, `∈@{A}`, `∉@{A}`, `##@{A}`, `⊆@{A}`, `⊂@{A}`,
  `⊑@{A}`, `≡ₚ@{A}` for being explicit about the type.
- A definition of basic telescopes `tele` and some theory about them.
- A simple type class based canceler `NatCancel` for natural numbers.
- A type `binder` for anonymous and named binders to be used in program language
  definitions with string-based binders.
- More results about `set_fold` on sets and multisets.
- Notions of infinite and finite predicates/sets and basic theory about them.
- New operation `map_seq`.
- The symmetric and reflexive/transitive/symmetric closure of a relation (`sc`
  and `rtsc`, respectively).
- Different notions of confluence (diamond property, confluence, local
  confluence) and the relations between these.
- A `size` function for finite maps and prove some properties.
- More results about `Qp` fractions.
- More miscellaneous results about sets, maps, lists, multisets.
- Various type class utilities, e.g. `TCEq`, `TCIf`, `TCDiag`, `TCNoBackTrack`,
  and `tc_to_bool`.
- Generalize `gset_to_propset` to `set_to_propset` for any `SemiSet`.

Changes:

- Consistently use `lia` instead of `omega` everywhere.
- Consistently block `simpl` on all `Z` operations.
- The `Infinite` class is now defined using a function `fresh : list A → A`
  that given a list `xs`, gives an element `fresh xs ∉ xs`.
- Make `default` an abbreviation for `from_option id` (instead of just swapping
  the argument order of `from_option`).
- More efficient `Countable` instance for `list` that is linear instead of
  exponential.
- Improve performance of `set_solver` significantly by introducing specialized
  type class `SetUnfoldElemOf` for propositions involving `∈`.
- Make `gset` a `Definition` instead of a `Notation` to improve performance.
- Use `disj_union` (notation `⊎`) for disjoint union on multisets (that adds the
  multiplicities). Repurpose `∪` on multisets for the actual union (that takes
  the max of the multiplicities).
- Set `Hint Mode` for `pretty`.

Naming:

- Consistently use the `set` prefix instead of the `collection` prefix for
  definitions and lemmas.
- Renaming of classes:
  + `Collection` into `Set_` (`_` since `Set` is a reserved keyword)
  + `SimpleCollection` into `SemiSet`
  + `FinCollection` into `FinSet`
  + `CollectionMonad` into `MonadSet`
- Types:
  + `set A := A → Prop` into `propset`
  + `bset := A → bool` into `boolset`.
- Files:
  + `collections.v` into `sets.v`
  + `fin_collections.v` into `fin_sets.v`
  + `bset` into `boolset`
  + `set` into `propset`
- Consistently use the naming scheme `X_to_Y` for conversion functions, e.g.
  `list_to_map` instead of the former `map_of_list`.

The following `sed` script should perform most of the renaming:

```
sed '
s/SimpleCollection/SemiSet/g;
s/FinCollection/FinSet/g;
s/CollectionMonad/MonadSet/g;
s/Collection/Set\_/g;
s/collection\_simple/set\_semi\_set/g;
s/fin\_collection/fin\_set/g;
s/collection\_monad\_simple/monad\_set\_semi\_set/g;
s/collection\_equiv/set\_equiv/g;
s/\bbset/boolset/g;
s/mkBSet/BoolSet/g;
s/mkSet/PropSet/g;
s/set\_equivalence/set\_equiv\_equivalence/g;
s/collection\_subseteq/set\_subseteq/g;
s/collection\_disjoint/set\_disjoint/g;
s/collection\_fold/set\_fold/g;
s/collection\_map/set\_map/g;
s/collection\_size/set\_size/g;
s/collection\_filter/set\_filter/g;
s/collection\_guard/set\_guard/g;
s/collection\_choose/set\_choose/g;
s/collection\_ind/set\_ind/g;
s/collection\_wf/set\_wf/g;
s/map\_to\_collection/map\_to\_set/g;
s/map\_of\_collection/set\_to\_map/g;
s/map\_of\_list/list\_to\_map/g;
s/map\_of\_to_list/list\_to\_map\_to\_list/g;
s/map\_to\_of\_list/map\_to\_list\_to\_map/g;
s/\bof\_list/list\_to\_set/g;
s/\bof\_option/option\_to\_set/g;
s/elem\_of\_of\_list/elem\_of\_list\_to\_set/g;
s/elem\_of\_of\_option/elem\_of\_option\_to\_set/g;
s/collection\_not\_subset\_inv/set\_not\_subset\_inv/g;
s/seq\_set/set\_seq/g;
s/collections/sets/g;
s/collection/set/g;
s/to\_gmap/gset\_to\_gmap/g;
s/of\_bools/bools\_to\_natset/g;
s/to_bools/natset\_to\_bools/g;
s/coPset\.of_gset/gset\_to\_coPset/g;
s/coPset\.elem\_of\_of\_gset/elem\_of\_gset\_to\_coPset/g;
s/of\_gset\_finite/gset\_to\_coPset\_finite/g;
s/set\_seq\_S\_disjoint/set\_seq\_S\_end\_disjoint/g;
s/set\_seq\_S\_union/set\_seq\_S\_end\_union/g;
s/map\_to\_of\_list/map\_to\_list\_to\_map/g;
s/of\_bools/bools\_to\_natset/g;
s/to\_bools/natset\_to\_bools/g;
' -i $(find -name "*.v")
```

## std++ 1.1.0 (released 2017-12-19)

Coq 8.5 is no longer supported by this release of std++.  Use std++ 1.0 if you
have to use Coq 8.5.

New features:

- Many new lemmas about lists, vectors, sets, maps.
- Equivalence proofs between std++ functions and their alternative in the the
  Coq standard library, e.g. `List.nth`, `List.NoDop`.
- Typeclass versions of the logical connectives and list predicates:
  `TCOr`, `TCAnd`, `TCTrue`, `TCForall`, `TCForall2`.
- A function `tc_opaque` to make definitions type class opaque.
- A type class `Infinite` for infinite types.
- A generic implementation to obtain fresh elements of infinite types.
- More theory about curry and uncurry functions on `gmap`.
- A generic `filter` and `zip_with` operation on finite maps.
- A type of generic trees for showing that arbitrary types are countable.

Changes:

- Get rid of `Automatic Coercions Import`, it is deprecated.
  Also get rid of `Set Asymmetric Patterns`.
- Various changes and improvements to `f_equiv` and `solve_proper`.
- `Hint Mode` is now set for all operational type classes to make instance
  search less likely to diverge.
- New type class `RelDecision` for decidable relations, and `EqDecision` is
  defined in terms of it. This class allows to set `Hint Mode` properly.
- Use the flag `assert` of `Arguments` to make it more robust.
- The functions `imap` and `imap2` on lists are defined so that they enjoy more
  definitional equalities.
- Theory about `fin` is moved to its own file `fin.v`.
- Rename `preserving` → `mono`.

Changes to notations:

- Operational type classes for lattice notations: `⊑`,`⊓`, `⊔`, `⊤` `⊥`.
- Replace `⊥` for disjointness with `##`, so that `⊥` can be used for the
  bottom lattice element.
- All notations are now in `stdpp_scope` with scope key `stdpp`
  (formerly `C_scope` and `C`).
- Higher precedence for `.1` and `.2` that is compatible with ssreflect.
- Various changes to monadic notations to improve compatibility with Mtac2:
  + Pattern matching notation for monadic bind `'pat ← x; y` where `pat` can
    be any Coq pattern.
  + Change the level of the do-notation.
  + `<$>` is left associative.
  + Notation `x ;; y` for `_ ← x; y`.

## History

Coq-std++ has originally been developed by Robbert Krebbers as part of his
formalization of the C programming language in his PhD thesis, called
[CH2O](http://robbertkrebbers.nl/thesis.html). After that, Coq-std++ has been
part of the [Iris project](http://iris-project.org), and has continued to be
developed by Robbert Krebbers, Ralf Jung, and Jacques Henri-Jourdan.
