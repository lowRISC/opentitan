
enum Foo { A, B, C };

Foo FailAvRule194(Foo a) {
  Foo result = A;
  switch (a) {
    case A:
      result = B;
      break;
    case B:
      result = A;
      break;
      // NOTE: No default
  }
  return result;
}
