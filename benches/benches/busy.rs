use benches::generate_bench;

generate_bench! {
    "create-mcslock-busy",
    "lock_unlock-mcslock-busy",
    "lock_unlock_read_contention-mcslock-busy",
    "lock_unlock_write_contention-mcslock-busy"
}
