struct SharedChaChaCore {
    state: Cell<[u32; 8]>,
    counter: AtomicU64; // Relaxed
    initialized: AtomicBool; // Release / Acquire
}

type AtomicCounter = AtomicU64;

const EMPTY: SharedChaChaCore = SharedChaChaCore {
    state: Cell::new([0u32; 8]);
    counter: ATOMIC_U64_INIT;
    initialized: ATOMIC_BOOL_INIT;
}

static GLOBAL_RNG: SharedChaChaCore = EMPTY;

impl SeedableRng for SharedChaChaCore {
    type Seed = [u8; SEED_WORDS*4];

    fn from_seed(seed: Self::Seed) -> Self {
        let mut seed_le = [0u32; SEED_WORDS];
        le::read_u32_into(&seed, &mut seed_le);
        GLOBAL_RNG.state.set(seed_le);
        GLOBAL_RNG.initialized.store(true, Ordering::Release);
    }
}



struct SharedChaChaCoreRef {}

impl BlockRngCore for SharedChaChaCoreRef {
    type Item = u32;
    type Results = [u32; 16];

    fn generate(&mut self, results: &mut Self::Results) {
        let rounds = (results.len() + 16 - 1) / 16;
        let counter = GLOBAL_RNG.counter.fetch_add(rounds, Ordering::Relaxed);
        let core = ChaChaCore {
            state: [0x61707865, 0x3320646E, 0x79622D32, 0x6B206574,
                    seed_le[0], seed_le[1], seed_le[2], seed_le[3], // FIXME
                    seed_le[4], seed_le[5], seed_le[6], seed_le[7], // FIXME
                    counter as u32, (counter >> 32) as u32, 0, 0],
        }
        core.generate(results)
    }
}



pub fn global_rng() -> GlobalRng {
    assert_eq!(GLOBAL_RNG.initialized.load(Ordering::Acquire), true);
}

#[derive(Clone, Debug)]
struct SharedChaChaRng {
    results: [u32; 16],
    index: usize,
    core: SharedChaChaCoreRef,
}


impl<R: BlockRngCore<Item=u32>> RngCore for BlockRng<R>
where <R as BlockRngCore>::Results: AsRef<[u32]> + AsMut<[u32]>
{
    #[inline(always)]
    fn next_u32(&mut self) -> u32 {
        if self.index >= self.results.as_ref().len() {
            self.generate_and_set(0);
        }

        let value = self.results.as_ref()[self.index];
        self.index += 1;
        value
    }

    #[inline(always)]
    fn next_u64(&mut self) -> u64 {
        let read_u64 = |results: &[u32], index| {
            if cfg!(any(target_arch = "x86", target_arch = "x86_64")) {
                // requires little-endian CPU supporting unaligned reads:
                unsafe { *(&results[index] as *const u32 as *const u64) }
            } else {
                let x = u64::from(results[index]);
                let y = u64::from(results[index + 1]);
                (y << 32) | x
            }
        };

        let len = self.results.as_ref().len();

        let index = self.index;
        if index < len-1 {
            self.index += 2;
            // Read an u64 from the current index
            read_u64(self.results.as_ref(), index)
        } else if index >= len {
            self.generate_and_set(2);
            read_u64(self.results.as_ref(), 0)
        } else {
            let x = u64::from(self.results.as_ref()[len-1]);
            self.generate_and_set(1);
            let y = u64::from(self.results.as_ref()[0]);
            (y << 32) | x
        }
    }

    // As an optimization we try to write directly into the output buffer.
    // This is only enabled for little-endian platforms where unaligned writes
    // are known to be safe and fast.
    #[cfg(any(target_arch = "x86", target_arch = "x86_64"))]
    fn fill_bytes(&mut self, dest: &mut [u8]) {
        let mut filled = 0;

        // Continue filling from the current set of results
        if self.index < self.results.as_ref().len() {
            let (consumed_u32, filled_u8) =
                fill_via_u32_chunks(&self.results.as_ref()[self.index..],
                                    dest);

            self.index += consumed_u32;
            filled += filled_u8;
        }

        let len_remainder =
            (dest.len() - filled) % (self.results.as_ref().len() * 4);
        let end_direct = dest.len() - len_remainder;

        while filled < end_direct {
            let dest_u32: &mut R::Results = unsafe {
                &mut *(dest[filled..].as_mut_ptr() as
                *mut <R as BlockRngCore>::Results)
            };
            self.core.generate(dest_u32);
            filled += self.results.as_ref().len() * 4;
            self.index = self.results.as_ref().len();
        }

        if len_remainder > 0 {
            self.core.generate(&mut self.results);
            let (consumed_u32, _) =
                fill_via_u32_chunks(self.results.as_ref(),
                                    &mut dest[filled..]);

            self.index = consumed_u32;
        }
    }

    #[cfg(not(any(target_arch = "x86", target_arch = "x86_64")))]
    fn fill_bytes(&mut self, dest: &mut [u8]) {
        let mut read_len = 0;
        while read_len < dest.len() {
            if self.index >= self.results.as_ref().len() {
                self.generate_and_set(0);
            }
            let (consumed_u32, filled_u8) =
                fill_via_u32_chunks(&self.results.as_ref()[self.index..],
                                    &mut dest[read_len..]);

            self.index += consumed_u32;
            read_len += filled_u8;
        }
    }

    fn try_fill_bytes(&mut self, dest: &mut [u8]) -> Result<(), Error> {
        self.fill_bytes(dest);
        Ok(())
    }
}





pub fn get_fork_counter() -> usize {
    RESEEDING_RNG_FORK_COUNTER.load(Ordering::Relaxed)
}

static FORK_HANDLER_REGISTERED: AtomicBool = ATOMIC_BOOL_INIT;

extern fn fork_handler() {
    // Note: fetch_add is defined to wrap on overflow
    // (which is what we want).
    RESEEDING_RNG_FORK_COUNTER.fetch_add(1, Ordering::Relaxed);
}



if self.index >= 16 {
    self.generate()
}

fn generate {
    let state = STATIC.state.get() (copy)
    let counter = counter.load(Ordering::Relaxed) // Correct ordering?
    let mut chacha = ChaChaCore { state: /* state + counter */ };
    let mut results = [u32; STATE_WORDS];
    chacha.generate(&mut results);
    // FIXME: assert counter is still the same or index >= 16
    {
        STATIC.results.set(results); // concurrent generates will just set it twice to the same value, because counter is the same.
        STATIC.counter.fetch_add(1)
    }
    // Announce a new set of results is available
    STATIC.index.store(0)
}

1) use values from stack
2) if stack is empty:
3) increment block counter
4) calculate results
5) push unused values onto a stack

// It is no problem if we lose some of the generated random numbers, but we should not never return the same value twice.

// stack size: nr_of_treads * max(unused_values) = block.len() - 1.
//             8 * 15 *4 = 480 bytes.


// We assume every call to `generate` uses at least one value of the results
// block. That leaves 15 unused values, that may be pushed onto the stack. We
// generously assume up to 8 threads are generating a block of results at the
// same time. With a stack size of 120 `u32`s (480 bytes) no values need to be
// thrown away in this scenario.
// FIXME: does rounding to a poer of two avoid bound checks?
const STACK_SIZE: usize = 8 * 15;
const STACK_INDEX_BITS: usize = 18;
const STACK_INDEX_MASK: usize = (1usize << STACK_INDEX_BITS) - 1;

struct ResultsStack {
    index: AtomicUsize;
    results: [Cell<u32>; STACK_SIZE]
}

impl ResultsStack {
    fn push(&mut self, src: &mut [u32]) -> bool {
        let index = self.index.load(Ordering::Relaxed);
        let slot = (index & STACK_INDEX_MASK) + 1;
        if slot >= STACK_SIZE {
            // Indicate trying to add any more values is not helpful, we would
            // just have to throw them away.
            return false;
        }
        self.results[slot] = value;
        // If another thread read a value in the meantime, or if it wrote to
        // the same slot as here, updating the index will fail.
        // That doesn't matter, it just means this value is thrown away.
        //
        // We don't have the ABA problem here, where other threads may have
        // also written to this slot, incremented index, used the value, and
        // decremented the index again. The reason is that `pop` does not simply
        // subtract 1, but also modifies some of the bits not used for the
        // index.
        let _ = self.index.compare_exchange(index,
                                            index + 1,
                                            Ordering::Release,
                                            Ordering::Relaxed);
        true;
    }

    fn pop(&mut self) -> Option<u32> {
        let mut slot;
        let mut done = false;
        loop {
            let index = self.index.load(Ordering:Relaxed);
            slot = index & STACK_INDEX_MASK;
            if slot == 0 { return None; } // FIXME: how to indicate empty?
            let new_index = index.wrapping_sub((1 | 1 << STACK_INDEX_BITS));
            if self.index.compare_exchange(index,
                                           new_index,
                                           Ordering::Acquire,
                                           Ordering::Relaxed).is_ok() {
                break();
            };
        }
        Some(self.results[slot])
    }
}

impl ResultsStack {
    fn push(&self, value: u32) -> bool {
        let index = self.index.load(Ordering::Relaxed);
        let slot = (index & STACK_INDEX_MASK) + 1;
        if slot >= STACK_SIZE {
            // Indicate trying to add any more values is not helpful, we would
            // just have to throw them away.
            return false;
        }
        self.results[slot].set(value);
        // If another thread read a value in the meantime, or if it wrote to
        // the same slot as here, updating the index will fail.
        // That doesn't matter, it just means this value is thrown away.
        //
        // We don't have the ABA problem here, where other threads may have
        // also written to this slot, incremented index, used the value, and
        // decremented the index again. The reason is that `pop` does not simply
        // subtract 1, but also modifies some of the bits not used for the
        // index.
        let _ = self.index.compare_exchange(index,
                                            index + 1,
                                            Ordering::Release,
                                            Ordering::Relaxed);
        true;
    }

    fn pop(&self) -> Option<u32> {
        let mut slot;
        let mut done = false;
        loop {
            let index = self.index.load(Ordering:Relaxed);
            slot = index & STACK_INDEX_MASK;
            if slot == 0 { return None; } // FIXME: how to indicate empty?
            let new_index = index.wrapping_sub((1 | 1 << STACK_INDEX_BITS));
            if self.index.compare_exchange(index,
                                           new_index,
                                           Ordering::Acquire,
                                           Ordering::Relaxed).is_ok() {
                break();
            };
        }
        Some(self.results[slot].get())
    }
}

// thread_rng(): populate results from ResultsStack
// Destructor: give back results







/// Atomic type holding a 64-bit counter. Uses `AtomicU64` on nightly,
/// and otherwise `AtomicUsize` on 64-bit architecture.
///
/// If `AtomicU64` is not available, and the architecture is 32-bit, it uses two
/// `AtomicUsize`. It is not possible to guarantee the counter increments
/// exactly with 1 without using locks. The `high` part of the counter may be
/// incremented more than once when the `low` part wraps around. What we do
/// guarantee is that the same counter is never returned twice before the `u64`
/// wraps around.
///
/// `fetch_increment` returns the current counter value as `(high, low)`, and
/// increments the counter for the next use.
#[cfg(all(feature = "nightly",
          target_has_atomic = "64"))]
struct AtomicCounter {
    counter: AtomicU64;
}

#[cfg(all(feature = "nightly",
          target_has_atomic = "64"))]
impl AtomicCounter {
    fn fetch_increment() -> (u32, u32) {
        let counter = self.counter.load(Ordering::Relaxed);
        ((counter >> 32) as u32, low as u32)
    }
}

#[cfg(all(not(feature = "nightly"),
          target_pointer_width = "64"))]
struct AtomicCounter {
    counter: AtomicUsize;
}

#[cfg(all(not(feature = "nightly"),
          target_pointer_width = "64"))]
impl AtomicCounter {
    fn fetch_increment() -> (u32, u32) {
        let counter = self.counter.load(Ordering::Relaxed) as u64;
        ((counter >> 32) as u32, low as u32)
    }
}

#[cfg(all(any(not(feature = "nightly"),
              all(feature = "nightly",
                  not(target_has_atomic = "64"))),
          target_pointer_width = "32"))]
struct AtomicCounter {
    low: AtomicUsize;
    high: AtomicUsize;
}

#[cfg(all(not(feature = "nightly"),
          target_pointer_width = "32"))]
impl AtomicCounter {
    fn fetch_increment() -> (u32, u32) {
        let high = self.high.load(Ordering::Relaxed);
        if self.low.load(Ordering::Relaxed) == ::core::usize::MAX {
            self.high.set(high + 1, Ordering::Relaxed);
        }
        let low = self.low.fetch_add(1, Ordering::Relaxed);
        (high, low)
    }
}


