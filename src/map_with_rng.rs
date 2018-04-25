
use {Rng, SeedableRng};

use rayon::iter::plumbing::{Consumer, Folder, Producer, ProducerCallback, UnindexedConsumer, UnindexedProducer};
use rayon::iter::{IndexedParallelIterator, ParallelIterator};

use std::fmt::{self, Debug};


/// `MapWith` is an iterator that transforms the elements of an underlying iterator.
///
/// This struct is created by the [`map_with()`] method on [`ParallelIterator`]
///
/// [`map_with()`]: trait.ParallelIterator.html#method.map_with
/// [`ParallelIterator`]: trait.ParallelIterator.html
#[must_use = "iterator adaptors are lazy and do nothing unless consumed"]
#[derive(Clone)]
pub struct MapWithRng<I: ParallelIterator, R, F> {
    base: I,
    rng: R,
    map_op: F,
}

impl<I: ParallelIterator + Debug, R: Debug, F> Debug for MapWithRng<I, R, F> {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        f.debug_struct("MapWithRng")
            .field("base", &self.base)
            .field("rng", &self.rng)
            .finish()
    }
}

/// Create a new `MapWith` iterator.
///
/// NB: a free fn because it is NOT part of the end-user API.
pub fn new<I, R, F>(base: I, rng: &mut R, map_op: F) -> MapWithRng<I, R, F>
    where I: ParallelIterator,
          R: Rng + SeedableRng,
{
    MapWithRng {
        base: base,
        rng: R::from_rng(rng).unwrap(), // FIXME: initial split?
        map_op: map_op,
    }
}

impl<I, R, F, B> ParallelIterator for MapWithRng<I, R, F>
    where I: ParallelIterator,
          R: Rng + SeedableRng + Clone + Send,
          F: Fn(&mut R, I::Item) -> B + Sync + Send,
          B: Send
{
    type Item = B;

    fn drive_unindexed<C>(self, consumer: C) -> C::Result
        where C: UnindexedConsumer<Self::Item>
    {
        let consumer1 =
            MapWithRngConsumer::new(consumer, self.rng, &self.map_op);
        self.base.drive_unindexed(consumer1)
    }

    fn opt_len(&self) -> Option<usize> {
        self.base.opt_len()
    }
}

impl<I, R, F, B> IndexedParallelIterator for MapWithRng<I, R, F>
    where I: IndexedParallelIterator,
          R: Rng + SeedableRng + Clone + Send,
          F: Fn(&mut R, I::Item) -> B + Sync + Send,
          B: Send
{
    fn drive<C>(self, consumer: C) -> C::Result
        where C: Consumer<Self::Item>
    {
        let consumer1 =
            MapWithRngConsumer::new(consumer, self.rng, &self.map_op);
        self.base.drive(consumer1)
    }

    fn len(&self) -> usize {
        self.base.len()
    }

    fn with_producer<CB>(self, callback: CB) -> CB::Output
        where CB: ProducerCallback<Self::Item>
    {
        return self.base.with_producer(Callback {
                                           callback: callback,
                                           rng: self.rng,
                                           map_op: self.map_op,
                                       });

        struct Callback<CB, U, F> {
            callback: CB,
            rng: U,
            map_op: F,
        }

        impl<T, U, F, R, CB> ProducerCallback<T> for Callback<CB, U, F>
            where CB: ProducerCallback<R>,
                  U: Rng + SeedableRng + Clone + Send,
                  F: Fn(&mut U, T) -> R + Sync,
                  R: Send
        {
            type Output = CB::Output;

            fn callback<P>(self, base: P) -> CB::Output
                where P: Producer<Item = T>
            {
                let producer = MapWithRngProducer {
                    base: base,
                    rng: self.rng,
                    split_level: 0,
                    map_op: &self.map_op,
                };
                self.callback.callback(producer)
            }
        }
    }
}

/// ////////////////////////////////////////////////////////////////////////

struct MapWithRngProducer<'f, P, U, F: 'f> {
    base: P,
    rng: U,
    split_level: u8,
    map_op: &'f F,
}

impl<'f, P, U, F, R> Producer for MapWithRngProducer<'f, P, U, F>
    where P: Producer,
          U: Rng + SeedableRng + Clone + Send,
          F: Fn(&mut U, P::Item) -> R + Sync,
          R: Send
{
    type Item = R;
    type IntoIter = MapWithRngIter<'f, P::IntoIter, U, F>;

    fn into_iter(self) -> Self::IntoIter {
        MapWithRngIter {
            base: self.base.into_iter(),
            rng: self.rng,
            map_op: self.map_op,
        }
    }

    fn min_len(&self) -> usize {
        self.base.min_len()
    }
    fn max_len(&self) -> usize {
        self.base.max_len()
    }

    fn split_at(self, index: usize) -> (Self, Self) {
        let (left, right) = self.base.split_at(index);
        let new_rng = U::split(&self.rng, self.split_level);
        (MapWithRngProducer {
             base: left,
             rng: self.rng,
             split_level: self.split_level + 1,
             map_op: self.map_op,
         },
         MapWithRngProducer {
             base: right,
             rng: new_rng,
             split_level: self.split_level + 1,
             map_op: self.map_op,
         })
    }

    fn fold_with<G>(self, folder: G) -> G
        where G: Folder<Self::Item>
    {
        let folder1 = MapWithRngFolder {
            base: folder,
            rng: self.rng,
            map_op: self.map_op,
        };
        self.base.fold_with(folder1).base
    }
}

struct MapWithRngIter<'f, I, U, F: 'f> {
    base: I,
    rng: U,
    map_op: &'f F,
}

impl<'f, I, U, F, R> Iterator for MapWithRngIter<'f, I, U, F>
    where I: Iterator,
          U: Rng + SeedableRng + Clone + Send,
          F: Fn(&mut U, I::Item) -> R + Sync,
          R: Send
{
    type Item = R;

    fn next(&mut self) -> Option<R> {
        self.base.next().map(|rng| (self.map_op)(&mut self.rng, rng))
    }

    fn size_hint(&self) -> (usize, Option<usize>) {
        self.base.size_hint()
    }
}

impl<'f, I, U, F, R> DoubleEndedIterator for MapWithRngIter<'f, I, U, F>
    where I: DoubleEndedIterator,
          U: Rng + SeedableRng + Clone + Send,
          F: Fn(&mut U, I::Item) -> R + Sync,
          R: Send
{
    fn next_back(&mut self) -> Option<R> {
        self.base.next_back().map(|rng| (self.map_op)(&mut self.rng, rng))
    }
}

impl<'f, I, U, F, R> ExactSizeIterator for MapWithRngIter<'f, I, U, F>
    where I: ExactSizeIterator,
          U: Rng + SeedableRng + Clone + Send,
          F: Fn(&mut U, I::Item) -> R + Sync,
          R: Send
{
}


/// ////////////////////////////////////////////////////////////////////////
/// Consumer implementation

struct MapWithRngConsumer<'f, C, U, F: 'f> {
    base: C,
    rng: U,
    split_level: u8,
    map_op: &'f F,
}

impl<'f, C, U, F> MapWithRngConsumer<'f, C, U, F> {
    fn new(base: C, rng: U, map_op: &'f F) -> Self {
        MapWithRngConsumer {
            base: base,
            rng: rng,
            split_level: 0,
            map_op: map_op,
        }
    }
}

impl<'f, T, U, R, C, F> Consumer<T> for MapWithRngConsumer<'f, C, U, F>
    where C: Consumer<R>,
          U: Rng + SeedableRng + Clone + Send,
          F: Fn(&mut U, T) -> R + Sync,
          R: Send
{
    type Folder = MapWithRngFolder<'f, C::Folder, U, F>;
    type Reducer = C::Reducer;
    type Result = C::Result;

    fn split_at(self, index: usize) -> (Self, Self, Self::Reducer) {
        let (left, right, reducer) = self.base.split_at(index);
        let new_rng = U::split(&self.rng, self.split_level);
        (MapWithRngConsumer {
             base: left,
             rng: self.rng,
             split_level: self.split_level + 1,
             map_op: self.map_op,
         },
         MapWithRngConsumer {
             base: right,
             rng: new_rng,
             split_level: self.split_level + 1,
             map_op: self.map_op,
         },
         reducer)
    }

    fn into_folder(self) -> Self::Folder {
        MapWithRngFolder {
            base: self.base.into_folder(),
            rng: self.rng,
            map_op: self.map_op,
        }
    }

    fn full(&self) -> bool {
        self.base.full()
    }
}

impl<'f, T, U, R, C, F> UnindexedConsumer<T> for MapWithRngConsumer<'f, C, U, F>
    where C: UnindexedConsumer<R>,
          U: Rng + SeedableRng + Clone + Send,
          F: Fn(&mut U, T) -> R + Sync,
          R: Send
{
    fn split_off_left(&self) -> Self {
        let new_rng = U::split(&self.rng, self.split_level);
        MapWithRngConsumer {
            base: self.base.split_off_left(),
            rng: new_rng,
            split_level: self.split_level + 1,
            map_op: self.map_op,
        }
    }

    fn to_reducer(&self) -> Self::Reducer {
        self.base.to_reducer()
    }
}

struct MapWithRngFolder<'f, C, U, F: 'f> {
    base: C,
    rng: U,
    map_op: &'f F,
}

impl<'f, T, U, R, C, F> Folder<T> for MapWithRngFolder<'f, C, U, F>
    where C: Folder<R>,
          U: SeedableRng,
          F: Fn(&mut U, T) -> R
{
    type Result = C::Result;

    fn consume(mut self, item: T) -> Self {
        let mapped_item = (self.map_op)(&mut self.rng, item);
        self.base = self.base.consume(mapped_item);
        self
    }

    fn consume_iter<I>(mut self, iter: I) -> Self
        where I: IntoIterator<Item = T>
    {
        {
            let map_op = self.map_op;
            let rng = &mut self.rng;
            let mapped_iter = iter.into_iter().map(|x| map_op(rng, x));
            self.base = self.base.consume_iter(mapped_iter);
        }
        self
    }

    fn complete(self) -> C::Result {
        self.base.complete()
    }

    fn full(&self) -> bool {
        self.base.full()
    }
}
