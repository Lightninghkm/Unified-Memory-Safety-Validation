# Copyright © 2024 Kaiming Huang
#
# Licensed under the Apache License, Version 2.0 (the "License");
# you may not use this file except in compliance with the License.
# You may obtain a copy of the License at
#
#     http://www.apache.org/licenses/LICENSE-2.0
#
# Unless required by applicable law or agreed to in writing, software
# distributed under the License is distributed on an "AS IS" BASIS,
# WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
# See the License for the specific language governing permissions and
# limitations under the License.

cmake_minimum_required(VERSION 3.4.3)

set(CMAKE_CXX_STANDARD 17)
set(CMAKE_CXX_STANDARD_REQUIRED ON)

project(UnifiedMemSafe)

find_package(LLVM REQUIRED CONFIG)

message(STATUS "Found LLVM ${LLVM_PACKAGE_VERSION}")
message(STATUS "Using LLVMConfig.cmake in: ${LLVM_DIR}")
message(STATUS "Using LLVM Library in: ${LLVM_LIBS}")
message(STATUS "Using LLVM Library in: ${LLVM_INCLUDE_DIRS}")

message("LLVM STATUS:
  Definitions ${LLVM_DEFINITIONS}
  Includes    ${LLVM_INCLUDE_DIRS}
  Libraries   ${LLVM_LIBRARY_DIRS}
  Targets     ${LLVM_TARGETS_TO_BUILD}"
)


include_directories(${LLVM_INCLUDE_DIRS})
link_directories(${LLVM_LIBRARY_DIRS})
add_definitions(${LLVM_DEFINITIONS})
set(NO_RTTI "-fno-rtti")
add_definitions(${NO_RTTI})
add_compile_options(-std=c++17) 

include_directories("${CMAKE_SOURCE_DIR}/program-dependence-graph/SVF/include")
include_directories("${CMAKE_SOURCE_DIR}/program-dependence-graph/include")

# Compiler flag
set(CMAKE_CXX_FLAGS "${CMAKE_CXX_FLAGS} -fno-rtti")

set(CMAKE_CXX_STANDARD 14 CACHE STRING "")

add_library(UnifiedMemSafe SHARED
    UnifiedMemSafe.cpp
    Utils.cpp
    Utils.hpp
    ValueRange.cpp
    ValueRange.hpp
    DataflowAnalysis.h
    PTAWrapper.hh
    PTAWrapper.cpp
    DataGuard.cpp
    DataGuard.hpp
    CompatibleType.cpp
    CompatibleType.hpp
    Uriah.cpp
    Uriah.hpp
    LLVMEssentials.hh
)

target_link_libraries(UnifiedMemSafe PUBLIC "${CMAKE_SOURCE_DIR}/program-dependence-graph/build/libpdg_shared.a")
target_link_libraries(UnifiedMemSafe PUBLIC "${CMAKE_SOURCE_DIR}/program-dependence-graph/SVF/Release-build/lib/libSvf.a")



if(APPLE)
    set_target_properties(UnifiedMemSafe PROPERTIES LINK_FLAGS "-undefined dynamic_lookup")
endif(APPLE)
