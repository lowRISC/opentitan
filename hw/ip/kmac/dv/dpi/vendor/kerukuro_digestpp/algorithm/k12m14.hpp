/*
This code is written by kerukuro and released into public domain.
*/

#ifndef DIGESTPP_ALGORITHM_K12M14_HPP
#define DIGESTPP_ALGORITHM_K12M14_HPP

#include "../hasher.hpp"
#include "detail/k12m14_provider.hpp"
#include "mixin/k12m14_mixin.hpp"

namespace digestpp
{

/**
 * @brief KangarooTwelve function
 *
 * Extendable output function similar to SHAKE128 but with reduced number of round.
 *
 * @xof
 *
 * @mixinparams customization
 *
 * @mixin{mixin::k12m14_mixin}
 *
 * @par Example:\n
 * @code // Absorb a string and squeeze 32 bytes of output
 * digestpp::k12 hasher;
 * hasher.absorb("The quick brown fox jumps over the lazy dog");
 * std::cout << hasher.hexsqueeze(32) << '\n';
 * @endcode
 *
 * @par Example output:\n
 * @code b4f249b4f77c58df170aa4d1723db1127d82f1d98d25ddda561ada459cd11a48
 * @endcode
 *
 * @sa hasher, mixin::k12m14_mixin
 */
typedef hasher<detail::k12m14_provider<128>, mixin::k12m14_mixin> k12;

/**
 * @brief MarsupilamiFourteen function
 *
 * Extendable output function similar to KangarooTwelve, but providing 256-bit security.
 *
 * @xof
 *
 * @mixinparams customization
 *
 * @mixin{mixin::k12m14_mixin}
 *
 * @par Example:\n
 * @code // Absorb a string and squeeze 32 bytes of output
 * digestpp::m14 hasher;
 * hasher.absorb("The quick brown fox jumps over the lazy dog");
 * std::cout << hasher.hexsqueeze(32) << '\n';
 * @endcode
 *
 * @par Example output:\n
 * @code 3611bcaa666347770dbffd4562f137c5adfe2e09f3c4268ef7c7d7c0e6c5d59c
 * @endcode
 *
 * @sa hasher, mixin::k12m14_mixin
 */
typedef hasher<detail::k12m14_provider<256>, mixin::k12m14_mixin> m14;

} // namespace digestpp

#endif // DIGESTPP_ALGORITHM_K12M14_HPP