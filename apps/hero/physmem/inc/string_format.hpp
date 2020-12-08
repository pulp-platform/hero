/** Copyright (c) 2015 iFreilicht
 *  SPDX-License-Identifier: CC0-1.0
 *  Source: https://stackoverflow.com/a/26221725
 *
 *  C++11-compatible String Formatting
 */

#ifndef HERO_STRING_FORMAT_H_
#define HERO_STRING_FORMAT_H_

#include <memory>
#include <stdexcept>
#include <string>

template<typename ... Args>
std::string string_format( const std::string& format, Args ... args )
{
    size_t size = snprintf( nullptr, 0, format.c_str(), args ... ) + 1; // Extra space for '\0'
    if( size <= 0 ){ throw std::runtime_error( "Error during formatting." ); }
    std::unique_ptr<char[]> buf( new char[ size ] );
    snprintf( buf.get(), size, format.c_str(), args ... );
    return std::string( buf.get(), buf.get() + size - 1 ); // We don't want the '\0' inside
}

#endif // HERO_STRING_FORMAT_H_
