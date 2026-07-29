#!/usr/bin/env python3
"""Generate fail-closed semantic mutations for the V285 ticket-spin proof."""

from pathlib import Path
import sys


def replace_once(source: str, old: str, new: str, label: str) -> str:
    count = source.count(old)
    if count != 1:
        raise ValueError(f"{label}: expected one match, found {count}")
    return source.replace(old, new, 1)


def main() -> None:
    if len(sys.argv) != 3:
        raise SystemExit("usage: generate_ticket_mutations.py INPUT.i OUTPUT_DIR")
    source = Path(sys.argv[1]).read_text()
    output = Path(sys.argv[2])
    output.mkdir(parents=True, exist_ok=True)

    cmpxchg = """    __atomic_compare_exchange_n(&a->_v, &exp, (vuint32_t)v, 0, 5,
                                5);"""
    acquire = """    if (tid == 3 - 1) {
        for (verification_loop_begin(); (verification_spin_start(), (!ticketlock_tryacquire(&lock)) ? 1 : (verification_spin_end(1), 0)); verification_spin_end(0)) {}
    } else {"""
    ticket = """    vuint32_t ticket = vatomic32_get_inc_rlx(&l->next);
    vatomic32_await_eq_acq(&l->owner, ticket);"""
    try_body = """    vuint32_t o = vatomic32_read_acq(&l->owner);
    vuint32_t n = vatomic32_cmpxchg_rlx(&l->next, o, o + 1);
    return n == o;"""

    mutations = {
        "m01_failure_shared_write": replace_once(
            source,
            cmpxchg,
            cmpxchg + "\n    if (exp != e) a->_v = exp + 1;",
            "m01",
        ),
        "m02_loop_carried_counter": replace_once(
            source,
            acquire,
            """    if (tid == 3 - 1) {
        vuint32_t attempts = 0;
        for (verification_loop_begin(); (verification_spin_start(), (!ticketlock_tryacquire(&lock)) ? 1 : (verification_spin_end(1), 0)); verification_spin_end(0)) { attempts++; }
    } else {""",
            "m02",
        ),
        "m03_missing_reservation": replace_once(
            source,
            ticket,
            """    vuint32_t ticket = vatomic32_read_rlx(&l->next);
    vatomic32_await_eq_acq(&l->owner, ticket);""",
            "m03",
        ),
        "m04_extra_unsafe_marked_loop": replace_once(
            source,
            acquire,
            """    if (tid == 3 - 1) {
        for (verification_loop_begin(); (verification_spin_start(), (!ticketlock_tryacquire(&lock)) ? 1 : (verification_spin_end(1), 0)); verification_spin_end(0)) {}
        for (verification_loop_begin(); (verification_spin_start(), (vatomic32_read_rlx(&lock.owner) != 0) ? 1 : (verification_spin_end(1), 0)); verification_spin_end(0)) { vatomic32_write_rlx(&lock.next, 7); }
    } else {""",
            "m04",
        ),
        "m05_success_updates_by_two": replace_once(
            source,
            try_body,
            """    vuint32_t o = vatomic32_read_acq(&l->owner);
    vuint32_t n = vatomic32_cmpxchg_rlx(&l->next, o, o + 2);
    return n == o;""",
            "m05",
        ),
        "m06_weak_compare_exchange": replace_once(
            source,
            cmpxchg,
            """    __atomic_compare_exchange_n(&a->_v, &exp, (vuint32_t)v, 1, 5,
                                5);""",
            "m06",
        ),
        "m07_destroy_expected_writeback": replace_once(
            source,
            cmpxchg,
            cmpxchg + "\n    exp = (vuint32_t)e;",
            "m07",
        ),
        "m08_failure_body_shared_write": replace_once(
            source,
            acquire,
            """    if (tid == 3 - 1) {
        for (verification_loop_begin(); (verification_spin_start(), (!ticketlock_tryacquire(&lock)) ? 1 : (verification_spin_end(1), 0)); verification_spin_end(0)) { vatomic32_write_rlx(&lock.next, 7); }
    } else {""",
            "m08",
        ),
        "m09_reverse_try_result": replace_once(
            source,
            try_body,
            """    vuint32_t o = vatomic32_read_acq(&l->owner);
    vuint32_t n = vatomic32_cmpxchg_rlx(&l->next, o, o + 1);
    return n != o;""",
            "m09",
        ),
        "m10_no_inner_wait": replace_once(
            source,
            ticket,
            """    vuint32_t ticket = vatomic32_get_inc_rlx(&l->next);
    (void)ticket;""",
            "m10",
        ),
    }

    for name, text in mutations.items():
        (output / f"{name}.i").write_text(text)
    print(f"generated={len(mutations)} output={output}")


if __name__ == "__main__":
    main()
