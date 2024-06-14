# Formalization of BBSL with Coq

## About BBSL (Bounding Box Specification Language)

BBSL is a formal language that specifies the spatial relation between bounding boxes in the given image.

## Environment

- The Coq Proof Assistant, version 8.13.2

## Installation

1. Install `Extra`
2. Install `BBSL`

### Build and install the library `Extra`

```bash
$ cd Extra

# build
$ make

# move the library `Extra` to /usr/lib/coq/user-contrib/
$ sudo make install
```

### Build and install the library `BBSL`

```bash
$ cd BBSL

$ make

$ sudo make install
```

## Examples

The examples can be run interactively in CoqIDE.

They requires to install this library in advance.

See [Installation](#installation).

- Examples/lead_vehicle_stopped.v

### References

- [1] 田中健人, 青木利晃, 川上大介, 千田伸男, 河井達治, & 冨田尭. (2020). 自動運転システムにおける画像を対象とした形式仕様記述言語 BBSL の提案. 研究報告ソフトウェア工学 (SE), 2020(8), 1-8.
- [2] 宇田拓馬. (2021). Coq による BBSL の形式化と検証.
- [3] Thorn, E., Kimmel, S. C., Chaka, M., & Hamilton, B. A. (2018). A framework for automated driving system testable cases and scenarios (No. DOT HS 812 623). United States. Department of Transportation. National Highway Traffic Safety Administration.
