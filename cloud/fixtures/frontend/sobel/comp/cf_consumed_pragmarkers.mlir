module {
  func.func @sobel(%arg0: memref<256xi32> {handshake.arg_name = "in"}, %arg1: memref<9xi32> {handshake.arg_name = "gX"}, %arg2: memref<9xi32> {handshake.arg_name = "gY"}, %arg3: memref<256xi32> {handshake.arg_name = "out"}) -> i32 {
    %c0_i32 = arith.constant {handshake.name = "constant0"} 0 : i32
    cf.br ^bb1(%c0_i32, %c0_i32 : i32, i32) {handshake.name = "br0"}
  ^bb1(%0: i32, %1: i32):  // 2 preds: ^bb0, ^bb11
    %c0_i32_0 = arith.constant {handshake.name = "constant9"} 0 : i32
    cf.br ^bb2(%0, %c0_i32_0 : i32, i32) {handshake.name = "br1"}
  ^bb2(%2: i32, %3: i32):  // 2 preds: ^bb1, ^bb10
    %c5_i32 = arith.constant {handshake.name = "constant10"} 5 : i32
    %4 = arith.cmpi slt, %3, %c5_i32 {handshake.name = "cmpi0"} : i32
    cf.cond_br %4, ^bb4, ^bb3 {handshake.name = "cond_br0"}
  ^bb3:  // pred: ^bb2
    %c5_i32_1 = arith.constant {handshake.name = "constant11"} 5 : i32
    %5 = arith.cmpi eq, %3, %c5_i32_1 {handshake.name = "cmpi1"} : i32
    cf.cond_br %5, ^bb10(%2 : i32), ^bb5 {handshake.name = "cond_br1"}
  ^bb4:  // pred: ^bb2
    %c0_i32_2 = arith.constant {handshake.name = "constant12"} 0 : i32
    %6 = arith.cmpi eq, %3, %c0_i32_2 {handshake.name = "cmpi2"} : i32
    cf.cond_br %6, ^bb10(%2 : i32), ^bb5 {handshake.name = "cond_br2"}
  ^bb5:  // 2 preds: ^bb3, ^bb4
    %c-1_i32 = arith.constant {handshake.name = "constant13"} -1 : i32
    %c0_i32_3 = arith.constant {handshake.name = "constant14"} 0 : i32
    %7 = arith.extui %3 {handshake.name = "extui0"} : i32 to i64
    %8 = arith.index_cast %7 {handshake.name = "index_cast0"} : i64 to index
    %9 = memref.load %arg0[%8] {handshake.name = "load0"} : memref<256xi32>
    %10 = arith.extui %3 {handshake.name = "extui1"} : i32 to i64
    %11 = arith.index_cast %10 {handshake.name = "index_cast1"} : i64 to index
    %12 = memref.load %arg0[%11] {handshake.name = "load1"} : memref<256xi32>
    cf.br ^bb6(%c-1_i32, %c0_i32_3, %c0_i32_3 : i32, i32, i32) {handshake.name = "br2"}
  ^bb6(%13: i32, %14: i32, %15: i32):  // 2 preds: ^bb5, ^bb8
    %c1_i32 = arith.constant {handshake.name = "constant15"} 1 : i32
    %c-1_i32_4 = arith.constant {handshake.name = "constant16"} -1 : i32
    %16 = arith.shli %13, %c1_i32 {handshake.name = "shli0"} : i32
    %17 = arith.addi %13, %16 {handshake.name = "addi13"} : i32
    %18 = arith.shli %13, %c1_i32 {handshake.name = "shli1"} : i32
    %19 = arith.addi %13, %18 {handshake.name = "addi14"} : i32
    cf.br ^bb7(%c-1_i32_4, %14, %15 : i32, i32, i32) {handshake.name = "br3"}
  ^bb7(%20: i32, %21: i32, %22: i32):  // 2 preds: ^bb6, ^bb7
    %c2_i32 = arith.constant {handshake.name = "constant17"} 2 : i32
    %c1_i32_5 = arith.constant {handshake.name = "constant18"} 1 : i32
    %c4_i32 = arith.constant {handshake.name = "constant19"} 4 : i32
    %23 = arith.addi %17, %20 {handshake.name = "addi0"} : i32
    %24 = arith.addi %23, %c4_i32 {handshake.name = "addi1"} : i32
    %25 = arith.index_cast %24 {handshake.name = "index_cast2"} : i32 to index
    %26 = memref.load %arg2[%25] {handshake.name = "load2"} : memref<9xi32>
    %27 = arith.muli %9, %26 {handshake.name = "muli2"} : i32
    %28 = arith.addi %21, %27 {handshake.name = "addi2"} : i32
    %29 = arith.addi %19, %20 {handshake.name = "addi3"} : i32
    %30 = arith.addi %29, %c4_i32 {handshake.name = "addi4"} : i32
    %31 = arith.index_cast %30 {handshake.name = "index_cast3"} : i32 to index
    %32 = memref.load %arg1[%31] {handshake.name = "load3"} : memref<9xi32>
    %33 = arith.muli %12, %32 {handshake.name = "muli3"} : i32
    %34 = arith.addi %22, %33 {handshake.name = "addi5"} : i32
    %35 = arith.addi %20, %c1_i32_5 {handshake.name = "addi6"} : i32
    %36 = arith.cmpi slt, %35, %c2_i32 {handshake.name = "cmpi3"} : i32
    cf.cond_br %36, ^bb7(%35, %28, %34 : i32, i32, i32), ^bb8(%34, %28 : i32, i32) {handshake.name = "cond_br3"}
  ^bb8(%37: i32, %38: i32):  // pred: ^bb7
    %c2_i32_6 = arith.constant {handshake.name = "constant20"} 2 : i32
    %c1_i32_7 = arith.constant {handshake.name = "constant21"} 1 : i32
    %39 = arith.addi %13, %c1_i32_7 {handshake.name = "addi7"} : i32
    %40 = arith.cmpi slt, %39, %c2_i32_6 {handshake.name = "cmpi4"} : i32
    cf.cond_br %40, ^bb6(%39, %38, %37 : i32, i32, i32), ^bb9(%37, %38 : i32, i32) {handshake.name = "cond_br4"}
  ^bb9(%41: i32, %42: i32):  // pred: ^bb8
    %c255_i32 = arith.constant {handshake.name = "constant22"} 255 : i32
    %c0_i32_8 = arith.constant {handshake.name = "constant23"} 0 : i32
    %43 = arith.cmpi sgt, %41, %c255_i32 {handshake.name = "cmpi5"} : i32
    %44 = arith.select %43, %c255_i32, %41 {handshake.name = "select0"} : i32
    %45 = arith.cmpi slt, %44, %c0_i32_8 {handshake.name = "cmpi6"} : i32
    %46 = arith.select %45, %c0_i32_8, %44 {handshake.name = "select1"} : i32
    %47 = arith.cmpi sgt, %42, %c255_i32 {handshake.name = "cmpi7"} : i32
    %48 = arith.select %47, %c255_i32, %42 {handshake.name = "select2"} : i32
    %49 = arith.cmpi slt, %48, %c0_i32_8 {handshake.name = "cmpi8"} : i32
    %50 = arith.select %49, %c0_i32_8, %48 {handshake.name = "select3"} : i32
    %51 = arith.addi %46, %50 {handshake.name = "addi8"} : i32
    %52 = arith.addi %2, %51 {handshake.name = "addi9"} : i32
    cf.br ^bb10(%52 : i32) {handshake.name = "br4"}
  ^bb10(%53: i32):  // 3 preds: ^bb3, ^bb4, ^bb9
    %c15_i32 = arith.constant {handshake.name = "constant24"} 15 : i32
    %c255_i32_9 = arith.constant {handshake.name = "constant25"} 255 : i32
    %c1_i32_10 = arith.constant {handshake.name = "constant26"} 1 : i32
    %54 = arith.andi %53, %c255_i32_9 {handshake.name = "andi0"} : i32
    %55 = arith.xori %54, %c255_i32_9 {handshake.name = "xori0"} : i32
    %56 = arith.addi %3, %1 {handshake.name = "addi10"} : i32
    %57 = arith.extui %56 {handshake.name = "extui2"} : i32 to i64
    %58 = arith.index_cast %57 {handshake.name = "index_cast4"} : i64 to index
    memref.store %55, %arg3[%58] {handshake.name = "store4"} : memref<256xi32>
    %59 = arith.addi %3, %c1_i32_10 {handshake.name = "addi11"} : i32
    %60 = arith.cmpi ult, %59, %c15_i32 {handshake.name = "cmpi9"} : i32
    cf.cond_br %60, ^bb2(%53, %59 : i32, i32), ^bb11(%53 : i32) {handshake.name = "cond_br5"}
  ^bb11(%61: i32):  // pred: ^bb10
    %c15_i32_11 = arith.constant {handshake.name = "constant27"} 15 : i32
    %c1_i32_12 = arith.constant {handshake.name = "constant28"} 1 : i32
    %62 = arith.addi %1, %c1_i32_12 {handshake.name = "addi12"} : i32
    %63 = arith.cmpi ult, %62, %c15_i32_11 {handshake.name = "cmpi10"} : i32
    cf.cond_br %63, ^bb1(%61, %62 : i32, i32), ^bb12(%61 : i32) {handshake.name = "cond_br6"}
  ^bb12(%64: i32):  // pred: ^bb11
    return {handshake.name = "return0"} %64 : i32
  }
}

