/*
This code is written by kerukuro and released into public domain.
*/

#ifndef DIGESTPP_ALGORITHM_MD5_HPP
#define DIGESTPP_ALGORITHM_MD5_HPP

#include "../hasher.hpp"
#include "detail/md5_provider.hpp"

namespace digestpp
{

/**
 * @brief MD5 hash function
 *
 * Note that MD5 hash function is considered insecure and is not recommended for new applications.
 *
 * @hash
 *
 * @outputsize 128 bits
 *
 * @defaultsize 128 bits
 *
 * @par Example:\n
 * @code // Output an MD5 digest of a string
 * digestpp::md5 hasher;
 * hasher.absorb("The quick brown fox jumps over the lazy dog");
 * std::cout << hasher.hexdigest() << '\n';
 * @endcode
 *
 * @par Example output:\n
 * @code 9e107d9d372bb6826bd81d3542a419d6
 * @endcode
 *
 * @sa hasher
 */
typedef hasher<detail::md5_provider> md5;

} // namespace digestpp

#endif