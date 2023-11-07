use std::{
    collections::{BTreeMap, HashMap},
    fmt::{self, Display, Formatter},
    iter::{once, repeat},
};

struct Relation {
    statement: Vec<char>,
    rows: Vec<Vec<Option<usize>>>,
}

impl Relation {
    fn new(rel: &str) -> Self {
        Self {
            statement: rel.chars().collect(),
            rows: Vec::new(),
        }
    }
}

struct Alg {
    rels: Vec<Relation>,
    // If Hn * g = Hn', (n, g) -> n'
    forward_map: HashMap<(usize, char), usize>,
    // If Hn * g = Hn', (g, n') -> n
    reverse_map: HashMap<(char, usize), usize>,
    num_cosets: usize,
}

impl Alg {
    fn new<'a>(coset: &str, rels: impl IntoIterator<Item = &'a str>) -> Self {
        let mut me = Self {
            rels: rels.into_iter().map(Relation::new).collect(),
            forward_map: HashMap::new(),
            reverse_map: HashMap::new(),
            num_cosets: 1,
        };

        for g in coset.chars() {
            me.forward_map.insert((0, g), 0);
            me.reverse_map.insert((g, 0), 0);
        }

        me.init_relations();
        me
    }

    fn solve(&mut self) {
        loop {
            self.init_relations();
            self.solve_step();
            println!("{}", self);
            if !self.create_coset() {
                break;
            }
        }
    }

    fn init_relations(&mut self) {
        for rel in &mut self.rels {
            rel.rows.extend((rel.rows.len()..self.num_cosets).map(|i| {
                once(Some(i))
                    .chain(repeat(None).take(rel.statement.len() - 1))
                    .chain(once(Some(i)))
                    .collect()
            }));
        }
    }

    fn solve_step(&mut self) {
        while self.fill_in_rows() {
            loop {
                if !self.merge_equivalent_cosets() {
                    break;
                }
            }
        }
    }

    fn fill_in_rows(&mut self) -> bool {
        let mut any_filled = false;
        loop {
            let mut cell_filled = false;
            for rel in &mut self.rels {
                for row in &mut rel.rows {
                    // Fill in the row moving left to right
                    for (j, (k, &g)) in (1..row.len() - 1).zip(rel.statement.iter().enumerate()) {
                        if row[j].is_some() {
                            continue;
                        }

                        let prev = match row[j - 1] {
                            Some(prev) => prev,
                            None => break,
                        };

                        if let Some(&next) = self.forward_map.get(&(prev, g)) {
                            row[j] = Some(next);

                            // Suppose we have the following scenario
                            //   g   h
                            // n   _   r
                            // and we fill in the blank with m. Then we learn that Hm * h = Hr
                            if let Some(next_next) = row[j + 1] {
                                let g = rel.statement[k + 1];
                                self.forward_map.insert((next, g), next_next);
                                self.reverse_map.insert((g, next_next), next);
                            }

                            cell_filled = true;
                        }
                    }

                    // Fill in the row moving right to left
                    for (j, (k, &g)) in (2..row.len())
                        .rev()
                        .zip(rel.statement.iter().enumerate().rev())
                    {
                        if row[j - 1].is_some() {
                            continue;
                        }

                        let next = match row[j] {
                            Some(next) => next,
                            None => break,
                        };

                        if let Some(&prev) = self.reverse_map.get(&(g, next)) {
                            row[j - 1] = Some(prev);

                            // Similar to comment in the loop above
                            if let Some(prev_prev) = row[j - 2] {
                                let g = rel.statement[k - 1];
                                self.forward_map.insert((prev_prev, g), prev);
                                self.reverse_map.insert((g, prev), prev_prev);
                            }

                            cell_filled = true;
                        }
                    }
                }
            }

            if cell_filled {
                any_filled = true;
            } else {
                return any_filled;
            }
        }
    }

    fn merge_equivalent_cosets(&mut self) -> bool {
        if self.num_cosets == 1 {
            return false;
        }

        let (coset, duplicate) = match self.find_equivalence() {
            Some(equiv) => equiv,
            None => return false,
        };

        println!("Found equivalence {coset} = {duplicate}");

        // Merge coset and duplicate, and shift all labels to be consecutive
        let mut translation = self
            .rels
            .iter()
            .flat_map(|rel| rel.rows.iter().flatten())
            .flatten()
            .copied()
            .map(|c| (if c == duplicate { coset } else { c }, 0))
            .collect::<BTreeMap<_, _>>();
        translation
            .iter_mut()
            .zip(0usize..)
            .for_each(|((_, value), next)| *value = next);
        let substitute = |c| {
            let c = if c == duplicate { coset } else { c };
            *translation.get(&c).unwrap()
        };

        for rel in &mut self.rels {
            for map in &mut rel.rows {
                for cell in map {
                    if let Some(entry) = cell.as_mut() {
                        *entry = substitute(*entry);
                    }
                }
            }

            rel.rows.sort_by_key(|map| map[0].unwrap());
            rel.rows.dedup_by_key(|map| map[0].unwrap());
        }

        self.forward_map = self
            .forward_map
            .iter()
            .map(|(&(prev, g), &next)| ((substitute(prev), g), substitute(next)))
            .collect();
        self.reverse_map = self
            .reverse_map
            .iter()
            .map(|(&(g, next), &prev)| ((g, substitute(next)), substitute(prev)))
            .collect();

        self.num_cosets = translation.len();

        true
    }

    fn find_equivalence(&self) -> Option<(usize, usize)> {
        let mut pfun = HashMap::new();

        for rel in &self.rels {
            for map in &rel.rows {
                for (pair, &g) in map.windows(2).zip(&rel.statement) {
                    let (forward, reverse) = pfun
                        .entry(g)
                        .or_insert_with(|| (HashMap::new(), HashMap::new()));
                    if let (Some(prev), Some(next)) = (pair[0], pair[1]) {
                        if let Some(confl_next) = forward.insert(prev, next) {
                            if confl_next != next {
                                return Some((
                                    usize::min(confl_next, next),
                                    usize::max(confl_next, next),
                                ));
                            }
                        }

                        if let Some(confl_prev) = reverse.insert(next, prev) {
                            if confl_prev != prev {
                                return Some((
                                    usize::min(confl_prev, prev),
                                    usize::max(confl_prev, prev),
                                ));
                            }
                        }
                    }
                }
            }
        }

        None
    }

    fn create_coset(&mut self) -> bool {
        for coset in 0..self.num_cosets {
            for rel in &mut self.rels {
                let row = &mut rel.rows[coset];
                for (i, &g) in (1..row.len() - 1).zip(&rel.statement) {
                    if row[i].is_none() {
                        let prev = match row[i - 1] {
                            Some(prev) => prev,
                            None => break,
                        };

                        let coset = self.num_cosets;
                        row[i] = Some(coset);
                        self.forward_map.insert((prev, g), coset);
                        self.reverse_map.insert((g, coset), prev);
                        self.num_cosets += 1;
                        return true;
                    }
                }
            }
        }
        false
    }
}

impl Display for Alg {
    fn fmt(&self, f: &mut Formatter<'_>) -> fmt::Result {
        write!(f, "  ")?;
        for rel in &self.rels {
            for &g in &rel.statement {
                write!(f, "{g:<3}")?;
            }
            write!(f, "   ")?;
        }
        writeln!(f)?;

        for coset in 0..self.num_cosets {
            for rel in &self.rels {
                for &e in &rel.rows[coset] {
                    match e {
                        Some(e) => write!(f, "{:<3}", e + 1)?,
                        None => write!(f, "_  ")?,
                    }
                }
            }
            writeln!(f)?;
        }

        Ok(())
    }
}

fn main() {
    let mut alg = Alg::new("x", ["xxx", "yyy", "xyxyyxxyy"]);
    alg.solve();
}
