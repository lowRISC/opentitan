#include <hwtrust/hwtrust.h>
#include <hwtrust/lib.rs.h>

using android::base::Error;
using android::base::Result;

namespace hwtrust {

rust::DiceChainKind convertKind(DiceChain::Kind kind) {
  switch (kind) {
    case DiceChain::Kind::kVsr13:
      return rust::DiceChainKind::Vsr13;
    case DiceChain::Kind::kVsr14:
      return rust::DiceChainKind::Vsr14;
    case DiceChain::Kind::kVsr15:
      return rust::DiceChainKind::Vsr15;
    case DiceChain::Kind::kVsr16:
      return rust::DiceChainKind::Vsr16;
  }
}

// The public API hides all rust deps from clients, so we end up with opaque, boxed types. This
// class standardizes the syntax for dealing with these types. How to...
// ...define a boxed opaque type:     struct BoxedFoo : Boxed<Foo, BoxedFoo> {};
// ...construct an object:            auto foo = BoxedFoo::moveFrom(boxed);
// ...dereference the inner object:   **foo;
template <typename BoxedT, typename DerivedT>
class Boxed {
public:
  Boxed(::rust::Box<BoxedT> b) : box_(std::move(b)) {}

  static std::unique_ptr<DerivedT> moveFrom(::rust::Box<BoxedT>& b) {
    return std::make_unique<DerivedT>(std::move(b));
  }

  const BoxedT &operator*() const noexcept { return *box_; }
  BoxedT &operator*() noexcept { return *box_; }

private:
  ::rust::Box<BoxedT> box_;
};

// Definition of the forward-declared boxed types.
struct BoxedDiceChain : Boxed<rust::DiceChain, BoxedDiceChain> {};
struct BoxedCsr : Boxed<rust::Csr, BoxedCsr> {};


// Define to satisfy unique_ptr.
DiceChain::~DiceChain() {}

DiceChain::DiceChain(std::unique_ptr<BoxedDiceChain> chain, size_t size) noexcept
      : chain_(std::move(chain)), size_(size) {}

DiceChain::DiceChain(DiceChain&& other) : DiceChain(std::move(other.chain_), other.size_) {}

Result<DiceChain> DiceChain::Verify(
  const std::vector<uint8_t>& chain, DiceChain::Kind kind, bool allow_any_mode,
  std::string_view instance) noexcept {
  rust::DiceChainKind chainKind = convertKind(kind);
  auto res = rust::VerifyDiceChain(
    {chain.data(), chain.size()}, chainKind, allow_any_mode, instance.data());
  if (!res.error.empty()) {
      return Error() << static_cast<std::string>(res.error);
  }
  return DiceChain(BoxedDiceChain::moveFrom(res.chain), res.len);
}

Result<std::vector<std::vector<uint8_t>>> DiceChain::CosePublicKeys() const noexcept {
  std::vector<std::vector<uint8_t>> result;
  for (auto i = 0; i < size_; ++i) {
    auto key = rust::GetDiceChainPublicKey(**chain_, i);
    if (key.empty()) {
      return Error() << "Failed to get public key from chain entry " << i;
    }
    result.emplace_back(key.begin(), key.end());
  }
  return result;
}

Result<bool> DiceChain::compareRootPublicKey(const DiceChain& other) const noexcept {
    auto result = rust::compareRootPublicKeyInDiceChain(**chain_, **other.chain_);
    if (!result.error.empty()) {
        return Error() << static_cast<std::string>(result.error);
    }
    return result.value;
}

Result<bool> DiceChain::componentNameContains(std::string_view value) const noexcept {
    auto result = rust::componentNameInDiceChainContains(**chain_, value.data());
    if (!result.error.empty()) {
        return Error() << static_cast<std::string>(result.error);
    }
    return result.value;
}

Result<bool> DiceChain::hasNonNormalMode() const noexcept {
    auto result = rust::hasNonNormalModeInDiceChain(**chain_);
    if (!result.error.empty()) {
        return Error() << static_cast<std::string>(result.error);
    }
    return result.value;
}

bool DiceChain::IsProper() const noexcept {
  return rust::IsDiceChainProper(**chain_);
}

// Define with a full definition of BoxedCsr to satisfy unique_ptr.
Csr::~Csr() {}

Csr::Csr(std::unique_ptr<BoxedCsr> csr, DiceChain::Kind kind, std::string_view instance) noexcept
    : mCsr(std::move(csr)), mKind(kind), mInstance(instance.data()) {}

Csr::Csr(Csr&& other) : Csr(std::move(other.mCsr), other.mKind, std::move(other.mInstance)) {}

Result<Csr> Csr::validate(const std::vector<uint8_t>& request, DiceChain::Kind kind, bool isFactory,
    bool allowAnyMode, std::string_view instance) noexcept {
    rust::DiceChainKind chainKind = convertKind(kind);
    auto result = rust::validateCsr(
        {request.data(), request.size()}, chainKind, isFactory, allowAnyMode, instance.data());
    if (!result.error.empty()) {
        return Error() << static_cast<std::string>(result.error);
    }
    return Csr(BoxedCsr::moveFrom(result.csr), kind, instance);
}

Result<DiceChain> Csr::getDiceChain() const noexcept {
    auto result = rust::getDiceChainFromCsr(**mCsr);
    if (!result.error.empty()) {
        return Error() << static_cast<std::string>(result.error);
    }
  return DiceChain(BoxedDiceChain::moveFrom(result.chain), result.len);
}

bool Csr::hasUdsCerts() const noexcept {
    return rust::csrHasUdsCerts(**mCsr);
}

Result<std::vector<uint8_t>> Csr::getCsrPayload() const noexcept {
    auto vector = rust::getCsrPayloadFromCsr(**mCsr);
    if (vector.empty()) {
        return Error() << "Failed to get CsrPayload";
    }
    return std::vector<uint8_t>{vector.begin(), vector.end()};
}

Result<bool> Csr::compareKeysToSign(const std::vector<uint8_t>& keysToSign) const noexcept {
    auto result = rust::compareKeysToSignInCsr(**mCsr, {keysToSign.data(), keysToSign.size()});
    if (!result.error.empty()) {
        return Error() << static_cast<std::string>(result.error);
    }
    return result.value;
}

Result<bool> Csr::compareChallenge(const std::vector<uint8_t>& challenge) const noexcept {
    auto result = rust::compareChallengeInCsr(**mCsr, {challenge.data(), challenge.size()});
    if (!result.error.empty()) {
        return Error() << static_cast<std::string>(result.error);
    }
    return result.value;
}

} // namespace hwtrust
