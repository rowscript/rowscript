use std::fmt::Formatter;

pub struct Iter<Iter> {
    iter: Iter,
}

impl<T> Iter<T> {
    pub fn new(iter: T) -> Iter<T> {
        Iter { iter }
    }
}

pub struct Pair<X, Y> {
    pair: (X, Y),
}

impl<X, Y> Pair<X, Y> {
    pub fn new(pair: (X, Y)) -> Pair<X, Y> {
        Pair { pair }
    }
}

pub struct Opt<'a, T> {
    option: &'a Option<T>,
}

impl<'a, T> Opt<'a, T> {
    pub fn new(option: &'a Option<T>) -> Opt<'a, T> {
        Opt { option }
    }
}

impl<'a, T, U> std::fmt::Display for Iter<U>
where
    T: std::fmt::Display,
    U: std::iter::Iterator<Item = T> + Clone,
{
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        f.write_str("'(")
            .and_then(|_| {
                let mut iter = self.iter.clone();
                if let Some(x) = iter.next() {
                    write!(f, "{}", x)?;
                }
                while let Some(x) = iter.next() {
                    write!(f, " {}", x)?;
                }
                Ok(())
            })
            .and_then(|_| f.write_str(")"))
    }
}

impl<X, Y> std::fmt::Display for Pair<X, Y>
where
    X: std::fmt::Display,
    Y: std::fmt::Display,
{
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        write!(f, "'({} {})", self.pair.0, self.pair.1)
    }
}

impl<'a, T> std::fmt::Display for Opt<'a, T>
where
    T: std::fmt::Display,
{
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        match self.option {
            None => write!(f, "'()"),
            Some(x) => write!(f, "'({})", x),
        }
    }
}
