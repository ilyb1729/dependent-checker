use super::name;

enum Kind {
    Star,
}

enum Info {
    HasKind(Kind),
    HasType(Type),
}

type Context = VecDeque<(Name, Info)>;


