function negate(x) /*: (U (num bool)) -> (U (num bool)) */ {
  if (typeof x == "number") {
    return 0 - x;
  } else {
    return !x;
  }
}
