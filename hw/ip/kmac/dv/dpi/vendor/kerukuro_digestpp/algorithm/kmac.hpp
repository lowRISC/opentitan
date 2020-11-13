/*
This code is written by kerukuro and released into public domain.
*/

#ifndef DIGESTPP_ALGORITHM_KMAC_HPP
#define DIGESTPP_ALGORITHM_KMAC_HPP

#include "../hasher.hpp"
#include "detail/kmac_provider.hpp"
#include "mixin/kmac_mixin.hpp"

namespace digestpp
{

/**
 * @brief KMAC128 in hash mode
 *
 * Use this variant when the required hash size is known in advance. Otherwise, use \ref kmac128_xof.
 * While primary usage of KMAC is message authentication, it can also be used without a key as a regular hash function.
 *
 * @hash
 *
 * @outputsize arbitrary
 *
 * @defaultsize none
 *
 * @throw std::runtime_error if the requested digest size is not divisible by 8 (full bytes)
 *
 * @mixinparams customization, key
 *
 * @mixin{mixin::kmac_mixin}
 *
 * @par Example:\n
 * @code // Set key and output a 256-bit KMAC128 of a string
 * digestpp::kmac128 hasher(256);
 * hasher.set_key(R"(@ABCDEFGHIJKLMNOPQRSTUVWXYZ[\]^_)");
 * hasher.absorb("The quick brown fox jumps over the lazy dog");
 * std::cout << hasher.hexdigest() << '\n';
 * @endcode
 *
 * @par Example output:\n
 * @code bbd4ebf20aacc8e4dfd2cc91f2b6cbf33e2a45d805996b48a17b8d3e42b4b010
 * @endcode
 *
 * @sa hasher, kmac128_xof, mixin::kmac_mixin
 */
typedef hasher<detail::kmac_provider<128, false>, mixin::kmac_mixin> kmac128;

/**
 * @brief KMAC256 in hash mode
 *
 * Use this variant when the required hash size is known in advance. Otherwise, use \ref kmac256_xof.
 * While primary usage of KMAC is message authentication, it can also be used without a key as a regular hash function.
 *
 * @hash
 *
 * @outputsize arbitrary
 *
 * @defaultsize none
 *
 * @throw std::runtime_error if the requested digest size is not divisible by 8 (full bytes)
 *
 * @mixinparams customization, key
 *
 * @mixin{mixin::kmac_mixin}
 *
 * @par Example:\n
 * @code // Set key and output a 256-bit KMAC256 of a string
 * digestpp::kmac256 hasher(256);
 * hasher.set_key(R("@ABCDEFGHIJKLMNOPQRSTUVWXYZ[\]^_"));
 * hasher.absorb("The quick brown fox jumps over the lazy dog");
 * std::cout << hasher.hexdigest() << '\n';
 * @endcode
 *
 * @par Example output:\n
 * @code bbe7d65fe0e7574254a13e0f3f79482275b96887287fc8b620a92ed5e5de3bce
 * @endcode
 *
 * @sa hasher, kmac256_xof, mixin::kmac_mixin
 */
typedef hasher<detail::kmac_provider<256, false>, mixin::kmac_mixin> kmac256;

/**
 * @brief KMAC128 in XOF mode (KMACXOF128)
 *
 * Use this variant when the required hash size is not known in advance. Otherwise, use \ref kmac128.
 * This hasher can also be used without a key, but there are no advantages over \ref cshake128 in this case.
 *
 * @xof
 *
 * @mixinparams customization, key
 *
 * @mixin{mixin::kmac_mixin}
 *
 * @par Example:\n
 * @code // Set key, absorb a string and squeeze 32 bytes of output
 * digestpp::kmac128_xof hasher;
 * hasher.set_key(R"(@ABCDEFGHIJKLMNOPQRSTUVWXYZ[\]^_)");
 * hasher.absorb("The quick brown fox jumps over the lazy dog");
 * std::cout << hasher.hexsqueeze(32) << '\n';
 * @endcode
 *
 * @par Example output:\n
 * @code a5dd2e2c92e4fe5d203ab7cc4e05df888b021390ba08a00dcb39a94ed07bd364
 * @endcode
 *
 * @sa hasher, kmac128, mixin::kmac_mixin
 */
typedef hasher<detail::kmac_provider<128, true>, mixin::kmac_mixin> kmac128_xof;

/**
 * @brief KMAC256 in XOF mode (KMACXOF256)
 *
 * Use this variant when the required hash size is not known in advance. Otherwise, use \ref kmac256.
 * This hasher can also be used without a key, but there are no advantages over \ref cshake256 in this case.
 *
 * @xof
 *
 * @mixinparams customization, key
 *
 * @mixin{mixin::kmac_mixin}
 *
 * @par Example:\n
 * @code // Set key, absorb a string and squeeze 32 bytes of output
 * digestpp::kmac256_xof hasher;
 * hasher.set_key(R"(@ABCDEFGHIJKLMNOPQRSTUVWXYZ[\]^_)");
 * hasher.absorb("The quick brown fox jumps over the lazy dog");
 * std::cout << hasher.hexsqueeze(32) << '\n';
 * @endcode
 *
 * @par Example output:\n
 * @code 81ce507692e27fb404e4a765c3be3450ce5c090a61b8311f93eb4e35604877ad
 * @endcode
 *
 * @sa hasher, kmac256, mixin::kmac_mixin
 */
typedef hasher<detail::kmac_provider<256, true>, mixin::kmac_mixin> kmac256_xof;

} // namespace digestpp

#endif // DIGESTPP_ALGORITHM_KMAC_HPP