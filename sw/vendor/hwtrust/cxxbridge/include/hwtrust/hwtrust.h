#pragma once

#include <memory>
#include <vector>

#include <android-base/result.h>

using android::base::Error;
using android::base::Result;

namespace hwtrust {

class Csr;

// Hide the details of the rust binding from clients with an opaque type.
struct BoxedDiceChain;

class DiceChain final {
public:
  friend Csr;

  enum class Kind {
    kVsr13,
    kVsr14,
    kVsr15,
    kVsr16,
  };

  static Result<DiceChain> Verify(
    const std::vector<uint8_t>& chain, DiceChain::Kind kind, bool allow_any_mode,
    std::string_view instance) noexcept;

  ~DiceChain();
  DiceChain(DiceChain&&);

  // The root public key (UDS public key) is not included here
  Result<std::vector<std::vector<uint8_t>>> CosePublicKeys() const noexcept;

  Result<bool> compareRootPublicKey(const DiceChain& other) const noexcept;

  // whether a certificate in the DICE chain has a non-normal mode
  Result<bool> hasNonNormalMode() const noexcept;

  Result<bool> componentNameContains(std::string_view value) const noexcept;

  bool IsProper() const noexcept;

private:
  DiceChain(std::unique_ptr<BoxedDiceChain> chain, size_t size) noexcept;

  std::unique_ptr<BoxedDiceChain> chain_;
  size_t size_;
};

struct BoxedCsr;

class Csr final {
public:
  static Result<Csr> validate(const std::vector<uint8_t>& csr, DiceChain::Kind kind, bool isFactory,
    bool allowAnyMode, std::string_view instance) noexcept;

  ~Csr();
  Csr(Csr&&);

  Result<DiceChain> getDiceChain() const noexcept;

  bool hasUdsCerts() const noexcept;

  Result<std::vector<uint8_t>> getCsrPayload() const noexcept;

  Result<bool> compareKeysToSign(const std::vector<uint8_t>& keysToSign) const noexcept;

  Result<bool> compareChallenge(const std::vector<uint8_t>& challenge) const noexcept;

  private:
    Csr(std::unique_ptr<BoxedCsr> csr, DiceChain::Kind kind, std::string_view instance) noexcept;

    std::unique_ptr<BoxedCsr> mCsr;
    const DiceChain::Kind mKind;
    const std::string mInstance;
};

} // namespace hwtrust
