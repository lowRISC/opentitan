/*
This code is written by kerukuro and released into public domain.
*/

#ifndef DIGESTPP_ALGORITHM_SHAKE_HPP
#define DIGESTPP_ALGORITHM_SHAKE_HPP

#include "../hasher.hpp"
#include "detail/shake_provider.hpp"
#include "mixin/cshake_mixin.hpp"

namespace digestpp
{

/**
 * @brief SHAKE128 function
 *
 * @xof
 *
 * @par Example:\n
 * @code // Absorb a string and squeeze 32 bytes of output
 * digestpp::shake128 hasher;
 * hasher.absorb("The quick brown fox jumps over the lazy dog");
 * std::cout << hasher.hexsqueeze(32) << '\n';
 * @endcode
 *
 * @par Example output:\n
 * @code f4202e3c5852f9182a0430fd8144f0a74b95e7417ecae17db0f8cfeed0e3e66e
 * @endcode
 *
 * @sa hasher, cshake128
 */
typedef hasher<detail::shake_provider<128, 24>> shake128;

/**
 * @brief SHAKE256 function
 *
 * @xof
 *
 * @par Example:\n
 * @code // Absorb a string and squeeze 32 bytes of output
 * digestpp::shake256 hasher;
 * hasher.absorb("The quick brown fox jumps over the lazy dog");
 * std::cout << hasher.hexsqueeze(32) << '\n';
 * @endcode
 *
 * @par Example output:\n
 * @code 2f671343d9b2e1604dc9dcf0753e5fe15c7c64a0d283cbbf722d411a0e36f6ca
 * @endcode
 *
 * @sa hasher, cshake256
 */
typedef hasher<detail::shake_provider<256, 24>> shake256;

/**
 * @brief Customizable cSHAKE128 function
 *
 * Extendable output function similar to SHAKE128 but with possibility to use a customization string.
 * When used without a customization string, the output is identical to \ref shake128.
 *
 * @xof
 *
 * @mixinparams function name, customization
 *
 * @mixin{mixin::cshake_mixin}
 *
 * @par Example:\n
 * @code // Absorb a string and squeeze 32 bytes of output
 * digestpp::cshake128 hasher;
 * hasher.set_customization("My Custom SHAKE");
 * hasher.absorb("The quick brown fox jumps over the lazy dog");
 * std::cout << hasher.hexsqueeze(32) << '\n';
 * @endcode
 *
 * @par Example output:\n
 * @code 5b831bfe752f7f05d81f18f0e83a92eb48b9e3d460c10022ecb4852aa8b1f9d4
 * @endcode
 *
 * @sa hasher, mixin::cshake_mixin
 */
typedef hasher<detail::shake_provider<128, 24>, mixin::cshake_mixin> cshake128;

/**
 * @brief Customizable cSHAKE256 function
 *
 * Extendable output function similar to SHAKE256 but with possibility to use a customization string.
 * When used without a customization string, the output is identical to \ref shake256.
 *
 * @xof
 *
 * @mixinparams function name, customization
 *
 * @mixin{mixin::cshake_mixin}
 *
 * @par Example:\n
 * @code // Absorb a string and squeeze 32 bytes of output
 * digestpp::cshake256 hasher;
 * hasher.set_customization("My Custom SHAKE");
 * hasher.absorb("The quick brown fox jumps over the lazy dog");
 * std::cout << hasher.hexsqueeze(32) << '\n';
 * @endcode
 *
 * @par Example output:\n
 * @code bcebde2c2e18f6efd99ee9e0def1383e86595d72e49b4754f7f727a962c3cd3d
 * @endcode
 *
 * @sa hasher, mixin::cshake_mixin
 */
typedef hasher<detail::shake_provider<256, 24>, mixin::cshake_mixin> cshake256;

} // namespace digestpp

#endif // DIGESTPP_ALGORITHM_SHAKE_HPP