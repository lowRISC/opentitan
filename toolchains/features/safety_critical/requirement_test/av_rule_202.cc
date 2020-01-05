
void NoOp() { return; }

void FailAvRule202() {
  float a = 1.0;
  float b = 2.0;
  if (a == b) {
    NoOp();
  }
}