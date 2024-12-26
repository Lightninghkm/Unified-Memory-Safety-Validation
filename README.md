# Unified Memory Safety Validation

This framework is the push-button solution of the combined memory safety validations of the [DataGuard](https://www.ndss-symposium.org/wp-content/uploads/2022-60-paper.pdf) and the [Uriah](https://dl.acm.org/doi/pdf/10.1145/3658644.3690310) frameworks.

## Installation
The framework is tested on [Ubuntu 20.04](https://releases.ubuntu.com/focal/), it has not been tested on other platforms up to now, so Ubuntu 20.04 is preferred.

### LLVM 10.0.0

This project implements the memory safety validation as an out-of-tree LLVM pass.

To compile an out-of-tree LLVM pass, the [prebuilt LLVM binaries](https://releases.llvm.org/download.html) are needed.

Or you can download them using apt:
```bash
sudo apt-get install llvm-10 clang-10
```

Make sure you specify the ```$PATH```s correctly.

### Build SVF

The SVF code is available in ```./program-dependence-graph/SVF```

To build SVF for alias analysis, run:

```bash
sudo apt install cmake gcc g++ libtinfo5 libz-dev libzstd-dev zip wget libncurses5-dev

cd ./program-dependence-graph/SVF 
source ./build.sh
```

### Build PDG

The PDG code is available in ```/program-dependence-graph```

```
cd ./program-dependence-graph
mkdir build
cd build
cmake ..
make
cd ..
```

### Build Validation

To build the memory safety validation pass, simply run:

```
cd ..
cmake .
make
```

Now you should be able to see the ```libUnifiedMemSafe.so``` in the root directory of this pass.

## Usage
This framework performs memory safety validation on the LLVM bitcode of the program that you would like to analyze.

In case you need help with building whole-program (or whole-library) LLVM bitcode files from an unmodified C or C++ source package that you would like to analyze, please see [wllvm](https://github.com/travitch/whole-program-llvm).

It's time to run the analysis and save the result in ```output.txt```:
```bash
opt-10 -load libUnifiedMemSafe.so -unified -disable-output < bitcode.bc > output.txt 2>&1
```

If you would like to print the results in cmd: 
```bash
opt-10 -load libUnifiedMemSafe.so -unified -disable-output < bitcode.bc
```

## Detailed Analysis Results
There are commented print statements in the source code of this framework in case you want to know more in addition to the default results, e.g., detailed information of unsafe objects. Uncomment those and you will get what you want :->.

## Tips
SVF modifies the original program's bitcode to facilitate its alias analysis by inserting instructions.

As a result, you may notice that the printed instructions have variable names with offsets compared to the original bitcode. For example, ```%100``` in the original bitcode might appear as ```%108``` in the analysis output. This behavior is unavoidable.

If you want to use the bitcode after the analysis for additional purposes, e.g., instrument the program with runtime checks, use the following command to obtain the resultant bitcode:

```bash
opt-10 -o output.bc -load libUnifiedMemSafe.so -unified < bitcode.bc
```

## Citations
If you want to use this analysis framework to boost your own research, or any other purposes, please consider to cite the following papers, thanks you!

```bash
@inproceedings{dataguard,
  Title                    = {The Taming of the Stack: Isolating Stack Data from Memory Errors},
  Author                   = {Kaiming Huang and Yongzhe Huang and Mathias Payer and Zhiyun Qian and Jack Sampson and Gang Tan and Trent Jaeger},
  Booktitle                = {Network and Distributed System Security Symposium},
  Year                     = {NDSS 2022},
  url_Paper = {https://www.cse.psu.edu/~trj1/papers/huang-ndss22.pdf},
  keywords  = {Software Security -> Inlined Reference Monitors (CFI; SFI; etc.)},
  numpages  = 17,
  publisher = {Internet Society},
}
```


```bash
@inproceedings{Uriah,
  author = {Huang, Kaiming and Payer, Mathias and Qian, Zhiyun and Sampson, Jack and Tan, Gang and Jaeger, Trent},
  title = {Top of the Heap: Efficient Memory Error Protection of Safe Heap Objects},
  year = {2024},
  isbn = {9798400706363},
  publisher = {Association for Computing Machinery},
  address = {New York, NY, USA},
  url = {https://doi.org/10.1145/3658644.3690310},
  doi = {10.1145/3658644.3690310},
  pages = {1330–1344},
  numpages = {15},
  keywords = {heap memory errors, memory safety, program analysis, secure allocator, software security, software-based fault isolation},
  location = {Salt Lake City, UT, USA},
  series = {CCS '24}
}
```


```bash
@article{ComprehensiveMemSafeValidation,
  author={Huang, Kaiming and Payer, Mathias and Qian, Zhiyun and Sampson, Jack and Tan, Gang and Jaeger, Trent},
  journal={ IEEE Security \& Privacy },
  title={{ Comprehensive Memory Safety Validation: An Alternative Approach to Memory Safety }},
  year={2024},
  volume={22},
  number={04},
  ISSN={1558-4046},
  pages={40-49},
  keywords={Safety;Runtime;Memory management;Protection;Costs;Static analysis;Software engineering},
  doi={10.1109/MSEC.2024.3379947},
  url = {https://doi.ieeecomputersociety.org/10.1109/MSEC.2024.3379947},
  publisher={IEEE Computer Society},
  address={Los Alamitos, CA, USA},
  month=jul}
}
```





