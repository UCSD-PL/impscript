function mkCounter() {
  var c = 0;
  return function () { c++; return c; };
};
10 + mkCounter()();
