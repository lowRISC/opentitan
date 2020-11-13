/*
This code is written by kerukuro and released into public domain.
*/

#ifndef DIGESTPP_ALGORITHM_SKEIN_HPP
#define DIGESTPP_ALGORITHM_SKEIN_HPP

#include "../hasher.hpp"
#include "detail/skein_provider.hpp"
#include "mixin/skein_mixin.hpp"

namespace digestpp
{

/**
 * @brief Skein1024 hash function
 *
 * Use this variant when the required hash size is known in advance. Otherwise, use \ref skein1024_xof
 *
 * @hash
 *
 * @outputsize arbitrary
 *
 * @defaultsize 1024 bits
 *
 * @throw std::runtime_error if the requested digest size is not divisible by 8 (full bytes)
 *
 * @mixinparams personalization, nonce, key
 *
 * @mixin{mixin::skein_mixin}
 *
 * @par Example:\n
 * @code // Output a 256-bit Skein1024 digest of a string
 * digestpp::skein1024 hasher(256);
 * hasher.absorb("The quick brown fox jumps over the lazy dog");
 * std::cout << hasher.hexdigest() << '\n';
 * @endcode
 *
 * @par Example output:\n
 * @code 054922d4393e36af62143986221555bee407671f6e57631bd7273e215a714833
 * @endcode
 *
 * @sa hasher, mixin::skein_mixin, skein1024_xof
 */
typedef hasher<detail::skein_provider<1024, false>, mixin::skein_mixin> skein1024;

/**
 * @brief Skein512 hash function
 *
 * Use this variant when the required hash size is known in advance. Otherwise, use \ref skein512_xof
 *
 * @hash
 *
 * @outputsize arbitrary
 *
 * @defaultsize 512 bits
 *
 * @throw std::runtime_error if the requested digest size is not divisible by 8 (full bytes)
 *
 * @mixinparams personalization, nonce, key
 *
 * @mixin{mixin::skein_mixin}
 *
 * @par Example:\n
 * @code // Output a 256-bit Skein512 digest of a string
 * digestpp::skein512 hasher(256);
 * hasher.absorb("The quick brown fox jumps over the lazy dog");
 * std::cout << hasher.hexdigest() << '\n';
 * @endcode
 *
 * @par Example output:\n
 * @code b3250457e05d3060b1a4bbc1428bc75a3f525ca389aeab96cfa34638d96e492a
 * @endcode
 *
 * @sa hasher, mixin::skein_mixin, skein512_xof
 */
typedef hasher<detail::skein_provider<512, false>, mixin::skein_mixin> skein512;

/**
 * @brief Skein256 hash function
 *
 * Use this variant when the required hash size is known in advance. Otherwise, use \ref skein256_xof
 *
 * @hash
 *
 * @outputsize arbitrary
 *
 * @defaultsize 256 bits
 *
 * @throw std::runtime_error if the requested digest size is not divisible by 8 (full bytes)
 *
 * @mixinparams personalization, nonce, key
 *
 * @mixin{mixin::skein_mixin}
 *
 * @par Example:\n
 * @code // Output a 512-bit Skein256 digest of a string
 * digestpp::skein256 hasher(512);
 * hasher.absorb("The quick brown fox jumps over the lazy dog");
 * std::cout << hasher.hexdigest() << '\n';
 * @endcode
 *
 * @par Example output:\n
 * @code f8138e72cdd9e11cf09e4be198c234acb0d21a9f75f936e989cf532f1fa9f4fb21d255811f0f1592fb3617d04704add875ae7bd16ddbbeaed4eca6eb9675d2c6
 * @endcode
 *
 * @sa hasher, mixin::skein_mixin, skein256_xof
 */
typedef hasher<detail::skein_provider<256, false>, mixin::skein_mixin> skein256;

/**
 * @brief Skein1024 in XOF mode
 *
 * Use this variant when the required hash size is not known in advance. Otherwise, use \ref skein1024
 *
 * @xof
 *
 * @mixinparams personalization, nonce, key
 *
 * @mixin{mixin::skein_mixin}
 *
 * @par Example:\n
 * @code // Absorb a string and squeeze 32 bytes of output
 * digestpp::skein1024_xof hasher;
 * hasher.absorb("The quick brown fox jumps over the lazy dog");
 * std::cout << hasher.hexsqueeze(32) << '\n';
 * @endcode
 *
 * @par Example output:\n
 * @code 20cd7366b0a3713037fdbf8c635ea190943261455689792a327d93a9fd74dedf
 * @endcode
 *
 * @sa hasher, mixin::skein_mixin, skein1024
 */
typedef hasher<detail::skein_provider<1024, true>, mixin::skein_mixin> skein1024_xof;

/**
 * @brief Skein512 in XOF mode
 *
 * Use this variant when the required hash size is not known in advance. Otherwise, use \ref skein512
 *
 * @xof
 *
 * @mixinparams personalization, nonce, key
 *
 * @mixin{mixin::skein_mixin}
 *
 * @par Example:\n
 * @code // Absorb a string and squeeze 32 bytes of output
 * digestpp::skein512_xof hasher;
 * hasher.absorb("The quick brown fox jumps over the lazy dog");
 * std::cout << hasher.hexsqueeze(32) << '\n';
 * @endcode
 *
 * @par Example output:\n
 * @code cd7447a48e387ca4461e75ede8424566f7ed816a80bfac5bed291ac107f96170
 * @endcode
 *
 * @sa hasher, mixin::skein_mixin, skein512
 */
typedef hasher<detail::skein_provider<512, true>, mixin::skein_mixin> skein512_xof;

/**
 * @brief Skein256 in XOF mode
 *
 * Use this variant when the required hash size is not known in advance. Otherwise, use \ref skein256
 *
 * @xof
 *
 * @mixinparams personalization, nonce, key
 *
 * @mixin{mixin::skein_mixin}
 *
 * @par Example:\n
 * @code // Absorb a string and squeeze 32 bytes of output
 * digestpp::skein256_xof hasher;
 * hasher.absorb("The quick brown fox jumps over the lazy dog");
 * std::cout << hasher.hexsqueeze(32) << '\n';
 * @endcode
 *
 * @par Example output:\n
 * @code 217021fbabe331c5753024fe4c17a005a698b037859ca8f4f0fb9112dce5605c
 * @endcode
 *
 * @sa hasher, mixin::skein_mixin, skein256
 */
typedef hasher<detail::skein_provider<256, true>, mixin::skein_mixin> skein256_xof;

} // namespace digestpp

#endif