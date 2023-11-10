use benches::generate_bench;

generate_bench! {
    "create-mcslock-yield",
    "lock_unlock-mcslock-yield",
    "lock_unlock_read_contention-mcslock-yield",
    "lock_unlock_write_contention-mcslock-yield"
}
