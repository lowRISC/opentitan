/*
This code is written by kerukuro and released into public domain.
*/

#ifndef DIGESTPP_ALGORITHM_BLAKE2_HPP
#define DIGESTPP_ALGORITHM_BLAKE2_HPP

#include "../hasher.hpp"
#include "detail/blake2_provider.hpp"
#include "mixin/blake2_mixin.hpp"

/// digestpp namespace
namespace digestpp
{

/**
 * @brief BLAKE2b hash function
 *
 * @hash
 *
 * @outputsize 8 - 512 bits
 *
 * @defaultsize 512 bits
 *
 * @throw std::runtime_error if the requested digest size is not divisible by 8 (full bytes),
 * or is not within the supported range
 *
 * @mixinparams salt, personalization, key
 *
 * @mixin{mixin::blake2_mixin}
 *
 * @par Example:\n
 * @code // Output a 256-bit BLAKE2b digest of a string
 * digestpp::blake2b hasher(256);
 * hasher.absorb("The quick brown fox jumps over the lazy dog");
 * std::cout << hasher.hexdigest() << '\n';
 * @endcode
 *
 * @par Example output:\n
 * @code 01718cec35cd3d796dd00020e0bfecb473ad23457d063b75eff29c0ffa2e58a9
 * @endcode
 *
 * @sa hasher, mixin::blake2_mixin
 */
typedef hasher<detail::blake2_provider<uint64_t, detail::blake2_type::hash>, mixin::blake2_mixin> blake2b;

/**
 * @brief BLAKE2s hash function
 *
 * @hash
 *
 * @outputsize 8 - 256 bits
 *
 * @defaultsize 256 bits
 *
 * @throw std::runtime_error if the requested digest size is not divisible by 8 (full bytes),
 * or is not within the supported range
 *
 * @mixinparams salt, personalization, key
 *
 * @mixin{mixin::blake2_mixin}
 *
 * @par Example:\n
 * @code // Output a 256-bit BLAKE2s digest of a string
 * digestpp::blake2s hasher;
 * hasher.absorb("The quick brown fox jumps over the lazy dog");
 * std::cout << hasher.hexdigest() << '\n';
 * @endcode
 *
 * @par Example output:\n
 * @code 606beeec743ccbeff6cbcdf5d5302aa855c256c29b88c8ed331ea1a6bf3c8812
 * @endcode
 *
 * @sa hasher, mixin::blake2_mixin
 */
typedef hasher<detail::blake2_provider<uint32_t, detail::blake2_type::hash>, mixin::blake2_mixin> blake2s;

/**
 * @brief BLAKE2xb hash function
 *
 * Use this variant when the required hash size is known in advance. Otherwise, use \ref blake2xb_xof
 *
 * @hash
 *
 * @outputsize arbitrary
 *
 * @defaultsize 512 bits
 *
 * @throw std::runtime_error if the requested digest size is not divisible by 8 (full bytes)
 *
 * @mixinparams salt, personalization, key
 *
 * @mixin{mixin::blake2_mixin}
 *
 * @par Example:\n
 * @code // Output a 256-bit BLAKE2xb digest of a string
 * digestpp::blake2xb hasher(256);
 * hasher.absorb("The quick brown fox jumps over the lazy dog");
 * std::cout << hasher.hexdigest() << '\n';
 * @endcode
 *
 * @par Example output:\n
 * @code ca7a0c9c54b4b93c0bee0aa3a4d63e4f7fb87e3e0a9050522377fde76f0b6c01
 * @endcode
 *
 * @sa hasher, mixin::blake2_mixin
 */
typedef hasher<detail::blake2_provider<uint64_t, detail::blake2_type::x_hash>, mixin::blake2_mixin> blake2xb;

/**
 * @brief BLAKE2xs hash function
 *
 * Use this variant when the required hash size is known in advance. Otherwise, use \ref blake2xs_xof
 *
 * @hash
 *
 * @outputsize arbitrary
 *
 * @defaultsize 256 bits
 *
 * @throw std::runtime_error if the requested digest size is not divisible by 8 (full bytes)
 *
 * @mixinparams salt, personalization, key
 *
 * @mixin{mixin::blake2_mixin}
 *
 * @par Example:\n
 * @code // Output a 512-bit BLAKE2xs digest of a string
 * digestpp::blake2xs hasher(512);
 * hasher.absorb("The quick brown fox jumps over the lazy dog");
 * std::cout << hasher.hexdigest() << '\n';
 * @endcode
 *
 * @par Example output:\n
 * @code e709f8377d21507c166e5dd2279a1f58b290792d65dafcc5647b6e439a974227503c341341572725709b874e95f13a438677aa6f9648467fd341e0f3e5421840
 * @endcode
 *
 * @sa hasher, mixin::blake2_mixin
 */
typedef hasher<detail::blake2_provider<uint32_t, detail::blake2_type::x_hash>, mixin::blake2_mixin> blake2xs;

/**
 * @brief BLAKE2xb in XOF mode
 *
 * Use this variant when the required hash size is not known in advance. Otherwise, use \ref blake2xb
 *
 * @xof
 *
 * @mixinparams salt, personalization, key
 *
 * @mixin{mixin::blake2_mixin}
 *
 * @par Example:\n
 * @code // Absorb a string and squeeze 32 bytes of output
 * digestpp::blake2xb_xof hasher;
 * hasher.absorb("The quick brown fox jumps over the lazy dog");
 * std::cout << hasher.hexsqueeze(32) << '\n';
 * @endcode
 *
 * @par Example output:\n
 * @code 364e84ca4c103df292306c93ebba6f6633d5e9cc8a95e040498e9a012d5ca534
 * @endcode
 *
 * @sa hasher, mixin::blake2_mixin
 */
typedef hasher<detail::blake2_provider<uint64_t, detail::blake2_type::xof>, mixin::blake2_mixin> blake2xb_xof;

/**
 * @brief BLAKE2xs in XOF mode
 *
 * Use this variant when the required hash size is not known in advance. Otherwise, use \ref blake2xs
 *
 * @xof
 *
 * @mixinparams salt, personalization, key
 *
 * @mixin{mixin::blake2_mixin}
 *
 * @par Example:\n
 * @code // Absorb a string and squeeze 32 bytes of output
 * digestpp::blake2xs_xof hasher;
 * hasher.absorb("The quick brown fox jumps over the lazy dog");
 * std::cout << hasher.hexsqueeze(32) << '\n';
 * @endcode
 *
 * @par Example output:\n
 * @code 0650cde4df888a06eada0f0fecb3c17594304b4a03fdd678182f27db1238b1747e33c34ae539fe2179a7594442b5cc9a7a0f398bb15ac3095a397de6a60061d6
 * @endcode
 *
 * @sa hasher, mixin::blake2_mixin
 */
typedef hasher<detail::blake2_provider<uint32_t, detail::blake2_type::xof>, mixin::blake2_mixin> blake2xs_xof;

} // namespace digestpp

#endif // DIGESTPP_ALGORITHM_BLAKE2_HPP