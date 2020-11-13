/*
This code is written by kerukuro and released into public domain.
*/

#ifndef DIGESTPP_ALGORITHM_GROESTL_HPP
#define DIGESTPP_ALGORITHM_GROESTL_HPP

#include "../hasher.hpp"
#include "detail/groestl_provider.hpp"

namespace digestpp
{

/**
 * @brief Grøstl hash function
 *
 * @hash
 *
 * @outputsize 8 - 512 bits
 *
 * @defaultsize none
 *
 * @throw std::runtime_error if the requested digest size is not divisible by 8 (full bytes),
 * or is not within the supported range
 *
 * @par Example:\n
 * @code // Output a 256-bit Grøstl digest of a string
 * digestpp::groestl hasher(256);
 * hasher.absorb("The quick brown fox jumps over the lazy dog");
 * std::cout << hasher.hexdigest() << '\n';
 * @endcode
 *
 * @par Example output:\n
 * @code 8c7ad62eb26a21297bc39c2d7293b4bd4d3399fa8afab29e970471739e28b301
 * @endcode
 *
 * @sa hasher
 */
typedef hasher<detail::groestl_provider> groestl;

} // namespace digestpp

#endif // DIGESTPP_ALGORITHM_GROESTL_HPP