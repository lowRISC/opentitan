
enum Foo { A, B };

Foo FailAvRule195(bool a) {
  Foo result = A;
  switch (a) {
    case true:
      result = B;
      break;
  }
  return B;
}
