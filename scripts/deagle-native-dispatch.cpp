/*******************************************************************\

Module: Native Deagle Engine Dispatch

\*******************************************************************/

#include <cerrno>
#include <cstring>
#include <fstream>
#include <iostream>
#include <regex>
#include <string>
#include <unistd.h>
#include <vector>

namespace
{
std::string executable_directory()
{
  std::vector<char> buffer(4096);
  const ssize_t length =
    readlink("/proc/self/exe", buffer.data(), buffer.size() - 1);
  if(length <= 0)
    return ".";
  buffer[static_cast<std::size_t>(length)] = '\0';
  const std::string path(buffer.data());
  const std::size_t slash = path.find_last_of('/');
  return slash == std::string::npos ? "." : path.substr(0, slash);
}

bool has_empty_compiler_barrier(const char *program_path)
{
  std::ifstream input(program_path);
  if(!input)
    return false;
  const std::string source(
    (std::istreambuf_iterator<char>(input)),
    std::istreambuf_iterator<char>());
  static const std::regex empty_barrier(
    R"(\b(?:__asm__|asm)\s*(?:__volatile__|volatile)?\s*\(\s*""\s*:::\s*"memory"\s*\))");
  return std::regex_search(source, empty_barrier);
}
} // namespace

int main(int argc, char **argv)
{
  if(argc < 2)
  {
    std::cerr << "Usage: deagle_exe <program> [options]\n";
    return 2;
  }

  const std::string directory = executable_directory();
  const std::string engine =
    directory +
    (has_empty_compiler_barrier(argv[1])
       ? "/deagle_pure_spin_exe"
       : "/deagle_core_exe");

  std::vector<char *> arguments;
  arguments.reserve(static_cast<std::size_t>(argc) + 1);
  arguments.push_back(const_cast<char *>(engine.c_str()));
  for(int index = 1; index < argc; ++index)
    arguments.push_back(argv[index]);
  arguments.push_back(nullptr);

  execv(engine.c_str(), arguments.data());
  std::cerr
    << "Failed to execute native Deagle engine " << engine << ": "
    << std::strerror(errno) << '\n';
  return 2;
}
