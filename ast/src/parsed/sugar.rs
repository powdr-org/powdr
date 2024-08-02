use super::Expression;

#[derive(Debug, PartialEq, Eq, PartialOrd, Ord, Clone)]
pub enum ArrayExpression {
    Value(Vec<Expression>),
    RepeatedValue(Vec<Expression>),
    Concat(Box<ArrayExpression>, Box<ArrayExpression>),
}

impl ArrayExpression {
    pub fn value(v: Vec<Expression>) -> Self {
        Self::Value(v)
    }

    pub fn repeated_value(v: Vec<Expression>) -> Self {
        Self::RepeatedValue(v)
    }

    pub fn concat(self, other: Self) -> Self {
        Self::Concat(Box::new(self), Box::new(other))
    }

    fn pad_with(self, pad: Expression) -> Self {
        Self::concat(self, Self::repeated_value(vec![pad]))
    }

    pub fn pad_with_zeroes(self) -> Self {
        self.pad_with(0u32.into())
    }

    fn last(&self) -> Option<&Expression> {
        match self {
            ArrayExpression::Value(v) => v.last(),
            ArrayExpression::RepeatedValue(v) => v.last(),
            ArrayExpression::Concat(_, right) => right.last(),
        }
    }

    // return None if `self` is empty
    pub fn pad_with_last(self) -> Option<Self> {
        self.last().cloned().map(|last| self.pad_with(last))
    }

    pub fn into_terms(self) -> Box<dyn Iterator<Item = Self>> {
        match self {
            Self::Concat(left, right) => Box::new(left.into_terms().chain(right.into_terms())),
            _ => Box::new(std::iter::once(self)),
        }
    }
}
