# Implementation plan: splitting IPs across two power domains

Companion to [split_ip_concept.md](split_ip_concept.md). That document defines *what* a split IP is; this one describes *how* to realize it in `reggen` and `topgen`, with concrete insertion points. All file/line references are to the current `split-ip-concept` branch and will drift — treat them as anchors, not gospel.

## Guiding decisions (from the concept discussion)

- **`partition` is intrinsic to the IP** → it is parsed and owned by `reggen` (identical for every instantiation) and forwarded to `topgen` as a read-only per-entry attribute. Precedent to mirror: `enabled_after_reset` on `Signal` (parsed in `reggen`, consumed in `merge.py`).
- **`domain` / `domain_secondary` are instance-level** → owned by `topgen` (a given IP type can land in different PDs at different tops), read from the module dict in `top_<top>.hjson`.
- **`domain` and `domain_secondary` may be equal** → a split IP can be instantiated with both partitions in a single PD; the intra-IP connections then stay inside that PD's wrapper (handled by the existing same-domain inter-module path — no special-casing).
- **Tooling stays PD-agnostic**: reason only about `domain` / `domain_secondary`; never hard-code Aon/Main or a gating direction.
- The `<ip>_part_primary` / `<ip>_part_secondary` RTL modules and the `<ip>_p2s_t` / `<ip>_s2p_t` structs in `<ip>_pkg` are **designer-provided**, not generated.

## Where each step plugs into the existing flow

`topgen.py::_process_top` order: `extract_clocks` (1279) → block creation → `elaborate_instance` (1290) → `connect_clocks` (1295) → `validate_top` (1303) → `merge_top` (1307) → `complete_topcfg` → `create_alert_lpgs` (1739) → `autoconnect` (1745) → `elab_intermodule` (1748). This runs inside a convergence loop (~1710-1736), so **every new step must be idempotent**.

---

## Phase 0 — `reggen` schema (IP-level static structure)

**0a. `is_split_ip` flag.** `util/reggen/ip_block.py`: add to `OPTIONAL_FIELDS` (94-150), parse with `check_bool` (default `False`), add a dataclass field, thread through the constructor call (405-409) and `_asdict` (549-588).

**0b. `partition` on list entries.** Add an optional `partition` key (values `primary`/`secondary`, default `primary`; `param_list` also accepts `both`). Add a small shared validator (membership check; there is no enum checker in `reggen/lib.py`, so validate with `check_str` + explicit set membership, raising `ValueError`).

| List | Class / file | Change |
|---|---|---|
| CIO (`available_input/output/inout_list`) | `Signal` — `util/reggen/signal.py:19` | add `"partition"` to `check_keys` optional list (21); store `self.partition`; **extend `as_nwt_dict` (55-67) to emit it** (interrupts/alerts/CIOs reach `topgen` only through this method) |
| `interrupt_list` | `Interrupt(Signal)` — `util/reggen/interrupt.py:30` | inherit / add `"partition"` to optional list (33) |
| `alert_list` | `Alert(Signal)` — `util/reggen/alert.py:19` | add `"partition"` to the (currently empty) optional list (21) |
| `inter_signal_list` | `InterSignal` — `util/reggen/inter_signal.py:31` | add to optional list (35) **and** to `_asdict` (77-90) |
| `param_list` | `BaseParam` — `util/reggen/params.py` | add `'partition'` to `OPTIONAL_FIELDS` (15-28), parse in `_parse_parameter` (128-268), add to `BaseParam.as_dict` (47-55); accept `both` |

Inter-signals and params already reach `topgen` via wholesale `_asdict()` / `as_dict()`, so only their serializers need the key. Interrupts/alerts/CIOs need the `as_nwt_dict` change because that method currently emits only `name`/`width`/`type`.

**0c. `clocking_secondary`.** `util/reggen/ip_block.py`: parse via `Clocking.from_raw` into a new optional dataclass field; register in `OPTIONAL_FIELDS`; thread constructor + `_asdict`. Add a `get_secondary_clock()` on `IpBlock` analogous to `get_primary_clock()`; note `Clocking.from_raw` enforces *exactly one* primary (104-106) — the secondary partition's clocking is a **separate** `Clocking` object, so that invariant is unaffected. Each `ClockingItem` already carries its own `reset`, so `clocking_secondary` fully describes both the secondary partition's clocks **and** resets — there is no separate `reset_secondary` key (mirrors how the primary partition's resets come from `clocking`). May be empty/absent when the secondary partition needs no clock/reset. Only meaningful when `is_split_ip`; validate that in topgen.

---

## Phase 1 — `topgen` validation + flat→nested normalization

**1a. Normalization (earliest step).** Add `normalize_partition_connections(topcfg)` in `merge.py`, run **before** `extract_clocks` (topgen.py:1279) so every downstream consumer sees the shape it expects. It only touches **split** instances (identified by the presence of `domain_secondary`); non-split instances are left byte-for-byte unchanged, so it is a guaranteed no-op for every current top.

For a split instance, the author-facing nested `{primary: …, secondary: …}` form of `reset_connections` / `clock_srcs` / `clock_group` is rewritten so that:
- the canonical key holds the **primary** (flat) value — exactly what the many existing partition-unaware consumers (`extract_clocks`, `validate_clock`/`validate_reset`, `amend_resets`, LPGs, `module_instantiations.tpl`) already read, so none of them need to change in this phase;
- a companion `<key>_secondary` key holds the secondary value, consumed only by the new split-IP-aware code added in Phase 3.

This deliberately avoids the original "normalize everything to `{primary: <flat>}`" idea, which would have forced simultaneous edits to every flat consumer (large regression surface across all tops). Idempotent (safe under the convergence loop): once split out, the canonical key is flat and re-running is a no-op. Runs before `validate_reset` (validate.py:1050-1054), which mutates `reset_connections` in place.

**1b. `util/topgen/validate.py`.**
- `module_optional` (267-326): add `domain_secondary`. `is_split_ip` is forwarded from the block during elaboration → add it to `module_added` (328-334) so `check_keys` accepts it.
- `check_power_domains` (1184-1203): require `domain_secondary` iff `is_split_ip`, forbid otherwise; validate membership in `top['power']['domains']`; assert `domain != domain_secondary` (v1).
- `validate_reset` (1017-1097) / `validate_clock` (1104-1147) / `check_clocks_resets` (931-975): branch on `is_split_ip` to validate each partition's connection sub-dict against **that partition's** PD (primary→`domain`, secondary→`domain_secondary`), including the per-connection `reset['domain']` check (1062-1065).

---

## Phase 2 — partition→domain resolution in `merge.py`

Helper `partition_domain(module, partition, default)` → `module['domain_secondary']` for `secondary`, else `module.get('domain', default)`.

- `elaborate_instance`: forwards `is_split_ip` onto the instance dict (only when true, to avoid perturbing non-split configs); `partition` already rides along on `param_list` (`as_dict`) and `inter_signal_list` (`_asdict`).
- `amend_interrupt`: interrupt `domain` now `partition_domain(module, signal.partition, default)` (uses the reggen `Interrupt.partition` attribute directly). The existing per-PD `count_pd` / chip-level `intr_vector_pd_*` logic keys off `irq["domain"]`, so it works unchanged once each interrupt carries its partition's PD.
- `amend_pinmux_io`: both the inter-PD CIO port creation loop and the three CIO domain-stamp sites now compute the PD per signal via `partition_domain(m, sig.partition, default)`. A non-split fast-path skip is preserved.

No-op for every non-split IP (all objects are `primary` → `partition_domain` returns the ordinary `domain`); verified with `make -k -C hw top_and_cmdgen` (zero `.gen.hjson` diff).

**Deferred to Phase 3:** alert connection domains. `commit_alert_connections` slices *all* of a module's alerts as one contiguous group in a single `m_domain`; splitting them per partition is a substantial rework tightly coupled with the LPG generalization, so it is done together in Phase 3.

---

## Phase 3 — clocking / reset / LPG + alert domains per partition

**Phase 3a (clocking + reset) — DONE.** `extract_clocks` refactored with an `elaborate_clock_srcs` inner helper, invoked for the primary partition and (when `clock_srcs_secondary` is present) the secondary partition → `clock_connections_secondary`. `amend_resets` registers the secondary partition's reset domains by walking `block.clocking_secondary.items` against `reset_connections_secondary`. `validate_reset`/`validate_clock` refactored to validate each partition's connections against that partition's clocking signals (reset-net domains are author-specified per entry, as for existing multi-PD modules). `connect_clocks` idle-clock search now spans both partitions' clocking items. Reset/clock-net domains are authored explicitly (dicts `{name, domain}`), not derived. Verified: split-aware validator unit tests + `make top_and_cmdgen` no-op. **Phase 3b (alerts/LPG) remains** (bullets below).

- `extract_clocks` (659-758): for a split IP, run the clock-group elaboration **twice** — primary using `clock_srcs[primary]` / `clock_group[primary]` / `domain`, secondary using `clock_srcs[secondary]` / `clock_group[secondary]` / `domain_secondary` and the block's `clocking_secondary`. Produce a nested `clock_connections` `{primary, secondary}`. Use `lib.get_clock_prefixes(top, <partition PD>)`.
- `connect_clocks` (761-846): iterate `clocking` **and** `clocking_secondary`.
- `amend_resets` (849-928): iterate `reset_connections` per partition (loop at 887-892); call `top_resets.add_reset_domain(reset['name'], reset['domain'])` with the partition's PD; use the secondary clock's reset (`get_secondary_clock()`) for the secondary partition.
- `commit_alert_connections` (~1304): **alert domains per partition (deferred from Phase 2).** Today it slices all `w = len(block.alerts)` alerts as one contiguous group in `m_domain = module['domain']`. Rework to group a split IP's alerts by their `partition`'s PD and slice/count each group into the handler separately (the `count_pd` / `connect_pd` / slice logic).
- `create_alert_lpgs` (942-...): **generalize the single-primary-clock assumption.** Today it uses one `block.get_primary_clock()` + the module's single reset/clock. For a split IP, compute an LPG per partition (primary via `get_primary_clock()`, secondary via `get_secondary_clock()` with the secondary clock group + reset + `domain_secondary`), and let each alert's `partition` select which partition's LPG it joins. This is the most involved single change.

---

## Phase 4 — `lib.py` filtering helpers

Change single-`domain` matches to "does this module have a partition in this PD?" (`m['domain'] == domain or m.get('domain_secondary') == domain`):
- `get_all_modules` — the primary emission driver; returns the one module dict in **both** PD passes.
- `find_modules`, `idx_of_last_module_with_params`.

Added `get_module_partition(m, domain)` → `'primary'`/`'secondary'` for the templates.

---

## Phase 5 — partition-aware filtering and instantiation

- `util/topgen/templates/toplevel_snippets/module_instantiations.tpl`: for each module returned by `get_all_modules(top, domain)`, emit `u_<name>_part_<partition>` of module type `<type>_part_<partition>`, indexing the partition's `clock_connections`/`reset_connections` and filtering interrupts / alerts / CIOs / inter-module signals to the emitted partition. Scan/DFT ports emit only for the primary partition.
- Same-PD support (added here): `lib.get_module_partitions(m, domain)` returns **both** partitions when they share a PD, and the template loops over them so both are emitted in one pass. The removal of the `domain != domain_secondary` check lives in `check_power_domains` (validate.py).
- `port_intermodule_signals.tpl` / `intermodule_signals.tpl`: unchanged — they already filter by signal `domain`, which is partition-correct once Phase 6 tags each signal's domain.

---

## Phase 6 — auto-connect split IPs: intra-IP structs + intermodule signalling

> **Ordering note:** an earlier draft of this plan scoped this work as "Phase 4" (before `lib.py`/templates). In practice it was implemented *after* them — the partitions must be emitted before the intra-IP crossing is meaningful to test — so it now sits as Phase 6, after `lib.py` (4) and templates (5). The corresponding commit was originally labelled "Phase7" and is renumbered to Phase6 in the rebase.

- **Partition-aware `domain` tagging** for the IP's own `inter_signal_list`: `get_signame_chip` (and the req/rsp resolution in `elab_intermodule`) now derive the domain from the signal's `partition` via `sig_partition_domain(module, sig)` (secondary → `domain_secondary`), so an inter-signal owned by the secondary partition is exposed from `domain_secondary`. Per the concept, inter-signals never route through the `p2s`/`s2p` structs.
- **Auto-connect the intra-IP `p2s`/`s2p` link** — `autoconnect_intra_ip(topcfg)` (called from `autoconnect`, before `elab_intermodule`) pairs, per split IP, a driver (act `req`) with a same-named receiver (act `rcv`) in the other partition and injects `<inst>.<sig>@<drv_part> → <inst>.<sig>@<rcv_part>`. The existing multi-PD machinery (`handle_multi_pd_intersig`) then auto-creates the chip-level signal + PD-level ports (cross-PD), or keeps the connection internal (same-PD).
- **Per-partition-unique signal names**: `filter_index` parses an optional `@partition` qualifier (returns a 4-tuple) and `find_intermodule_signal(..., partition)` filters by it, so the two same-named driver/receiver ends of an intra-IP signal resolve unambiguously. Non-qualified references are byte-identical to before.

---

## Pilot IP (rstmgr) + end-to-end verification

Pilot IP chosen: **rstmgr** — the alert/CPU crash-dump capture logic moves into a secondary partition in the Main PD (primary stays Aon).

1. `hw/ip_templates/rstmgr`: `is_split_ip` + `clocking_secondary` in `rstmgr.hjson.tpl`; real `rstmgr_interpart_p2s_t`/`rstmgr_interpart_s2p_t` structs in `rstmgr_pkg.sv.tpl`; `interpart_p2s`/`interpart_s2p` inter-signals (one per partition, same name); a pseudo secondary alert `fatal_sec_test`; RTL split into `rstmgr_part_primary.sv.tpl` and `rstmgr_part_secondary.sv`; `rstmgr.core.tpl` filelist updated.
2. All three tops' `rstmgr` instances gain nested `clock_srcs`/`reset_connections`/`clock_group` + `domain_secondary`.

### Verification (performed)
- **Backwards-compat**: `make -k -C hw top_and_cmdgen` — no-op diff for non-split IPs (caught and fixed a `default=vars` leak in Phase 0 via class-level attribute defaults).
- **Generation**: inspected generated PD tops — `rstmgr_part_primary` in `earlgrey_pd_aon.sv`, `rstmgr_part_secondary` in `earlgrey_pd_main.sv`, crash-dump moved, `interpart_p2s`/`s2p` crossing the PD boundary via chip-level nets; secondary alert on a Main LPG.
- **Same-PD**: temporarily retargeting the secondary to Aon emits both partitions in one wrapper with internal interpart nets (no chip-level crossing).
- **Elaboration**: `./bazelisk.sh build --//hw/top=earlgrey //hw:verilator_real` → exit 0 (elaboration-first; CDC across the Aon↔Main crossing is a follow-up).

### Follow-up (not yet done)
- CDC synchronizers for the crash-dump register interface across the Aon↔Main boundary.
