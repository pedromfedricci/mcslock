use std::sync::Arc;
use std::thread;

use criterion::{black_box, Bencher};
use mcslock::raw::{Mutex, MutexNode};

pub fn gen_create(bencher: &mut Bencher) {
    bencher.iter(|| {
        let value = black_box(0);
        Mutex::new(value)
    });
}

pub fn gen_lock_unlock(bencher: &mut Bencher) {
    let mut node = MutexNode::new();
    let mutex = Mutex::new(0_u32);

    bencher.iter(|| {
        let mut guard = mutex.lock(&mut node);
        *guard = guard.wrapping_add(1);
        drop(guard);
    })
}

pub fn gen_lock_unlock_read_contention(bencher: &mut Bencher) {
    let data = Arc::new(Mutex::new(0_u32));

    let thread = thread::spawn({
        let data = Arc::clone(&data);
        let mut node = MutexNode::new();

        move || {
            while Arc::strong_count(&data) > 1 {
                for _ in 0..1000 {
                    black_box(*data.lock(&mut node));
                }
            }
        }
    });

    let mut node = MutexNode::new();
    bencher.iter(|| {
        let mut data = data.lock(&mut node);
        *data = data.wrapping_add(1);
        drop(data);
    });

    drop(data);
    thread.join().unwrap();
}

pub fn gen_lock_unlock_write_contention(bencher: &mut Bencher) {
    let data = Arc::new(Mutex::new(0_u32));

    let thread = std::thread::spawn({
        let data = Arc::clone(&data);
        let mut node = MutexNode::new();

        move || {
            while Arc::strong_count(&data) > 1 {
                for _ in 0..1000 {
                    let mut m = data.lock(&mut node);
                    *m = m.wrapping_add(1);
                    drop(m);
                }
            }
        }
    });

    let mut node = MutexNode::new();
    bencher.iter(|| {
        let mut m = data.lock(&mut node);
        *m = m.wrapping_add(1);
        drop(m);
    });

    drop(data);
    thread.join().unwrap();
}

#[macro_export]
macro_rules! generate_bench {
    ($create:literal, $lock_unlock:literal, $read_cont:literal, $write_cont:literal) => {
        use criterion::{criterion_group, criterion_main, Criterion};
        use $crate::*;

        fn create(criterion: &mut Criterion) {
            criterion.bench_function($create, |bench| gen_create(bench));
        }

        fn lock_unlock(criterion: &mut Criterion) {
            criterion.bench_function($lock_unlock, |bench| gen_lock_unlock(bench));
        }

        fn lock_unlock_read_contention(criterion: &mut Criterion) {
            criterion.bench_function($read_cont, |bench| gen_lock_unlock_read_contention(bench));
        }

        fn lock_unlock_write_contention(criterion: &mut Criterion) {
            criterion.bench_function($write_cont, |bench| gen_lock_unlock_write_contention(bench));
        }

        criterion_group!(
            mutex,
            create,
            lock_unlock,
            lock_unlock_read_contention,
            lock_unlock_write_contention,
        );

        criterion_main!(mutex);
    };
}
