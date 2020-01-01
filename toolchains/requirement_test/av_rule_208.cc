void FailAvRule208() {
  try {
    throw 20;
  } catch (int e) {
    e++;
  }
  return;
}