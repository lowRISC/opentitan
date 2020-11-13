/*
This code is written by kerukuro and released into public domain.
*/

#ifndef DIGESTPP_ALGORITHM_BLAKE_HPP
#define DIGESTPP_ALGORITHM_BLAKE_HPP

#include "../hasher.hpp"
#include "detail/blake_provider.hpp"
#include "mixin/blake_mixin.hpp"

namespace digestpp
{

/**
 * @brief BLAKE hash function (SHA-3 finalist)
 *
 * @hash
 *
 * @outputsize 224 / 256 / 384 / 512 bits
 *
 * @defaultsize none
 *
 * @throw std::runtime_error if the requested digest size is not supported
 *
 * @mixinparams salt
 *
 * @mixin{mixin::blake_mixin}
 *
 * @par Example:\n
 * @code // Output a 256-bit BLAKE digest of a string
 * digestpp::blake hasher(256);
 * hasher.absorb("The quick brown fox jumps over the lazy dog");
 * std::cout << hasher.hexdigest() << '\n';
 * @endcode
 *
 * @par Example output:\n
 * @code 7576698ee9cad30173080678e5965916adbb11cb5245d386bf1ffda1cb26c9d7
 * @endcode
 *
 * @sa hasher, mixin::blake_mixin
 */
typedef hasher<detail::blake_provider, mixin::blake_mixin> blake;

} // namespace digestpp

#endif // DIGESTPP_ALGORITHM_BLAKE_HPP