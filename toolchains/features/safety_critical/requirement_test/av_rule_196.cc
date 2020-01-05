enum Foo { A, B };

Foo FailAvRule196(Foo a) {
  Foo result = A;
  switch (a) {
    case A:
      result = B;
      break;
      // Note: only 1 case
    default:
      break;
  }
  return result;
}
