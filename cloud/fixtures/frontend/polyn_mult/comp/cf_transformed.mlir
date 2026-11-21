module {
  func.func @polyn_mult(%arg0: memref<100xi32> {handshake.arg_name = "a"}, %arg1: memref<100xi32> {handshake.arg_name = "b"}, %arg2: memref<100xi32> {handshake.arg_name = "out"}) -> i32 {
    %c0_i32 = arith.constant {handshake.name = "constant0"} 0 : i32
    cf.br ^bb1(%c0_i32 : i32) {handshake.name = "br0"}
  ^bb1(%0: i32):  // 2 preds: ^bb0, ^bb5
    %c1_i32 = arith.constant {handshake.name = "constant3"} 1 : i32
    %c100_i32 = arith.constant {handshake.name = "constant4"} 100 : i32
    %c0_i32_0 = arith.constant {handshake.name = "constant5"} 0 : i32
    %1 = arith.extui %0 {handshake.name = "extui0"} : i32 to i64
    %2 = arith.index_cast %1 {handshake.name = "index_cast0"} : i64 to index
    memref.store %c0_i32_0, %arg2[%2] {handshake.deps = #handshake<deps[{dstAccess : "load3", loopDepth : 0, distance : 0, isActive : true}, {dstAccess : "load7", loopDepth : 0, distance : 0, isActive : true}, {dstAccess : "store4", loopDepth : 0, distance : 0, isActive : true}, {dstAccess : "store8", loopDepth : 0, distance : 0, isActive : true}]>, handshake.name = "store0"} : memref<100xi32>
    %3 = arith.subi %c100_i32, %0 {handshake.name = "subi0"} : i32
    %4 = arith.cmpi ugt, %3, %c1_i32 {handshake.name = "cmpi0"} : i32
    cf.cond_br %4, ^bb2(%c1_i32 : i32), ^bb3 {handshake.name = "cond_br0"}
  ^bb2(%5: i32):  // 2 preds: ^bb1, ^bb2
    %c1_i32_1 = arith.constant {handshake.name = "constant6"} 1 : i32
    %c100_i32_2 = arith.constant {handshake.name = "constant7"} 100 : i32
    %6 = arith.addi %0, %5 {handshake.name = "addi0"} : i32
    %7 = arith.extui %6 {handshake.name = "extui1"} : i32 to i64
    %8 = arith.index_cast %7 {handshake.name = "index_cast1"} : i64 to index
    %9 = memref.load %arg0[%8] {handshake.name = "load1"} : memref<100xi32>
    %10 = arith.subi %c100_i32_2, %5 {handshake.name = "subi1"} : i32
    %11 = arith.extui %10 {handshake.name = "extui2"} : i32 to i64
    %12 = arith.index_cast %11 {handshake.name = "index_cast2"} : i64 to index
    %13 = memref.load %arg1[%12] {handshake.name = "load2"} : memref<100xi32>
    %14 = arith.muli %9, %13 {handshake.name = "muli0"} : i32
    %15 = arith.extui %0 {handshake.name = "extui3"} : i32 to i64
    %16 = arith.index_cast %15 {handshake.name = "index_cast3"} : i64 to index
    %17 = memref.load %arg2[%16] {handshake.name = "load3"} : memref<100xi32>
    %18 = arith.addi %17, %14 {handshake.name = "addi1"} : i32
    %19 = arith.index_cast %15 {handshake.name = "index_cast4"} : i64 to index
    memref.store %18, %arg2[%19] {handshake.deps = #handshake<deps[{dstAccess : "store0", loopDepth : 0, distance : 0, isActive : true}, {dstAccess : "load3", loopDepth : 0, distance : 0, isActive : true}, {dstAccess : "load7", loopDepth : 0, distance : 0, isActive : true}, {dstAccess : "store8", loopDepth : 0, distance : 0, isActive : true}]>, handshake.name = "store4"} : memref<100xi32>
    %20 = arith.addi %5, %c1_i32_1 {handshake.name = "addi2"} : i32
    %21 = arith.cmpi ult, %20, %3 {handshake.name = "cmpi1"} : i32
    cf.cond_br %21, ^bb2(%20 : i32), ^bb3 {handshake.name = "cond_br1"}
  ^bb3:  // 2 preds: ^bb1, ^bb2
    %c1_i32_3 = arith.constant {handshake.name = "constant8"} 1 : i32
    %c0_i32_4 = arith.constant {handshake.name = "constant9"} 0 : i32
    %22 = arith.addi %0, %c1_i32_3 {handshake.name = "addi3"} : i32
    cf.br ^bb4(%c0_i32_4 : i32) {handshake.name = "br1"}
  ^bb4(%23: i32):  // 2 preds: ^bb3, ^bb4
    %c1_i32_5 = arith.constant {handshake.name = "constant10"} 1 : i32
    %24 = arith.subi %0, %23 {handshake.name = "subi2"} : i32
    %25 = arith.extui %24 {handshake.name = "extui4"} : i32 to i64
    %26 = arith.index_cast %25 {handshake.name = "index_cast5"} : i64 to index
    %27 = memref.load %arg0[%26] {handshake.name = "load5"} : memref<100xi32>
    %28 = arith.extui %23 {handshake.name = "extui5"} : i32 to i64
    %29 = arith.index_cast %28 {handshake.name = "index_cast6"} : i64 to index
    %30 = memref.load %arg1[%29] {handshake.name = "load6"} : memref<100xi32>
    %31 = arith.muli %27, %30 {handshake.name = "muli1"} : i32
    %32 = arith.extui %0 {handshake.name = "extui6"} : i32 to i64
    %33 = arith.index_cast %32 {handshake.name = "index_cast7"} : i64 to index
    %34 = memref.load %arg2[%33] {handshake.name = "load7"} : memref<100xi32>
    %35 = arith.addi %34, %31 {handshake.name = "addi4"} : i32
    %36 = arith.index_cast %32 {handshake.name = "index_cast8"} : i64 to index
    memref.store %35, %arg2[%36] {handshake.deps = #handshake<deps[{dstAccess : "store0", loopDepth : 0, distance : 0, isActive : true}, {dstAccess : "store4", loopDepth : 0, distance : 0, isActive : true}, {dstAccess : "load7", loopDepth : 0, distance : 0, isActive : true}]>, handshake.name = "store8"} : memref<100xi32>
    %37 = arith.addi %23, %c1_i32_5 {handshake.name = "addi5"} : i32
    %38 = arith.cmpi ult, %37, %22 {handshake.name = "cmpi2"} : i32
    cf.cond_br %38, ^bb4(%37 : i32), ^bb5(%37 : i32) {handshake.name = "cond_br2"}
  ^bb5(%39: i32):  // pred: ^bb4
    %c1_i32_6 = arith.constant {handshake.name = "constant11"} 1 : i32
    %c100_i32_7 = arith.constant {handshake.name = "constant12"} 100 : i32
    %40 = arith.addi %39, %0 {handshake.name = "addi6"} : i32
    %41 = arith.addi %0, %c1_i32_6 {handshake.name = "addi7"} : i32
    %42 = arith.cmpi ult, %41, %c100_i32_7 {handshake.name = "cmpi3"} : i32
    cf.cond_br %42, ^bb1(%41 : i32), ^bb6(%40 : i32) {handshake.name = "cond_br3"}
  ^bb6(%43: i32):  // pred: ^bb5
    return {handshake.name = "return0"} %43 : i32
  }
}

