function foo(xs) {
  1 + xs.hd;
  2 + xs.hd;
  3 + xs.tl.hd;
  4 + xs.tl.hd;
  5 + xs.tl.tl.hd;
  6 + xs.tl.tl.hd;
  return xs.hd + xs.tl.hd + xs.tl.tl.hd;
}
