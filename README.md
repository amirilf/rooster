### [**Software Foundations**](https://softwarefoundations.cis.upenn.edu/)

- **LF** - Logical Foundations
- **PLF** - Programming Language Foundations
- **VFA** - Verified Functional Algorithms
- **QC** - QuickChick
- **VC** - Verifiable C
- **SLF** - Separation Logic Foundations
- **SECF** - Security Foundations

#### Usage

```bash
./run.sh build          # Build all files
./run.sh file <path>    # Build specific file
./run.sh clean          # Clean compiled files
```

#### Structure

```
lf/                     # Logical Foundations
├── ch01_basics/
└── ch02_induction/
└── ...
plf/                    # Programming Language Foundations
└── ch01_equiv/
...
```

#### Imports

```coq
From SF Require Import lf.ch01_basics.p01_days.
From SF Require Import {book}.ch{num}_{name}.p{num}_{name}.
```

#### VSCode

Run `./run.sh build` before using VsRocq! it requires compiled `.vo` files to resolve imports.<br>
Without compiled files, you'll see errors like:

```
Cannot find a physical path bound to logical path
lf.ch01_basics.p01_days with prefix SF.
```

If you have compiled files but are still seeing those frustrating red errors, try changing the import line and then changing it back, or restart VsRocq.
