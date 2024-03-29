/*
 * Copyright (C) 2018 ETH Zurich and University of Bologna
 *
 * Licensed under the Apache License, Version 2.0 (the "License");
 * you may not use this file except in compliance with the License.
 * You may obtain a copy of the License at
 *
 *     http://www.apache.org/licenses/LICENSE-2.0
 *
 * Unless required by applicable law or agreed to in writing, software
 * distributed under the License is distributed on an "AS IS" BASIS,
 * WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
 * See the License for the specific language governing permissions and
 * limitations under the License.
 */

#ifndef __ARCHI_UDMA_UDMA_PERIPH_V3_H__
#define __ARCHI_UDMA_UDMA_PERIPH_V3_H__

/*
 * TCDM
 */
#ifdef ARCHI_UDMA_HAS_TCDM

#define TCDM_T_DST_SADDR                (0x0)
#define TCDM_T_SRC_SADDR                (0x4)

#endif



/*
 * CAM
 */
#ifdef ARCHI_UDMA_HAS_CAM

// CAM custom registers offset definition
#define CAM_GLOB_OFFSET                  (0x00)
#define CAM_LL_OFFSET                    (0x04)
#define CAM_UR_OFFSET                    (0x08)
#define CAM_SIZE_OFFSET                  (0x0C)
#define CAM_FILTER_OFFSET                (0x10)

// CAM custom registers bitfields offset, mask, value definition
#define CAM_CFG_GLOB_FRAMEDROP_EN_OFFSET    0
#define CAM_CFG_GLOB_FRAMEDROP_EN_WIDTH     1
#define CAM_CFG_GLOB_FRAMEDROP_EN_MASK      (0x1 << CAM_CFG_GLOB_FRAMEDROP_EN_OFFSET)
#define CAM_CFG_GLOB_FRAMEDROP_EN_ENA     (1 << CAM_CFG_GLOB_FRAMEDROP_EN_OFFSET)
#define CAM_CFG_GLOB_FRAMEDROP_EN_DIS     (0 << CAM_CFG_GLOB_FRAMEDROP_EN_OFFSET)

#define CAM_CFG_GLOB_FRAMEDROP_VAL_OFFSET   1
#define CAM_CFG_GLOB_FRAMEDROP_VAL_WIDTH    6
#define CAM_CFG_GLOB_FRAMEDROP_VAL_MASK     (0x3f << CAM_CFG_GLOB_FRAMEDROP_VAL_OFFSET)
#define CAM_CFG_GLOB_FRAMEDROP_VAL(val)     (val << CAM_CFG_GLOB_FRAMEDROP_VAL_OFFSET)

#define CAM_CFG_GLOB_FRAMESLICE_EN_OFFSET   7
#define CAM_CFG_GLOB_FRAMESLICE_EN_WIDTH    1
#define CAM_CFG_GLOB_FRAMESLICE_EN_MASK   (0x1 << CAM_CFG_GLOB_FRAMESLICE_EN_OFFSET)
#define CAM_CFG_GLOB_FRAMESLICE_EN_ENA    (1 << CAM_CFG_GLOB_FRAMESLICE_EN_OFFSET)
#define CAM_CFG_GLOB_FRAMESLICE_EN_DIS    (0 << CAM_CFG_GLOB_FRAMESLICE_EN_OFFSET)

#define CAM_CFG_GLOB_FORMAT_OFFSET          8
#define CAM_CFG_GLOB_FORMAT_WIDTH         2
#define CAM_CFG_GLOB_FORMAT_MASK          (0x7 << CAM_CFG_GLOB_FORMAT_OFFSET)
#define CAM_CFG_GLOB_FORMAT_RGB565        (0 << CAM_CFG_GLOB_FORMAT_OFFSET)
#define CAM_CFG_GLOB_FORMAT_RGB555        (1 << CAM_CFG_GLOB_FORMAT_OFFSET)
#define CAM_CFG_GLOB_FORMAT_RGB444        (2 << CAM_CFG_GLOB_FORMAT_OFFSET)
#define CAM_CFG_GLOB_FORMAT_BYPASS_LITEND   (4 << CAM_CFG_GLOB_FORMAT_OFFSET)
#define CAM_CFG_GLOB_FORMAT_BYPASS_BIGEND   (5 << CAM_CFG_GLOB_FORMAT_OFFSET)

#define ARCHI_CAM_CFG_GLOB_FORMAT_RGB565          0
#define ARCHI_CAM_CFG_GLOB_FORMAT_RGB555          1
#define ARCHI_CAM_CFG_GLOB_FORMAT_RGB444          2
#define ARCHI_CAM_CFG_GLOB_FORMAT_BYPASS_LITEND   4
#define ARCHI_CAM_CFG_GLOB_FORMAT_BYPASS_BIGEND   5

#define CAM_CFG_GLOB_SHIFT_OFFSET           11
#define CAM_CFG_GLOB_SHIFT_WIDTH          4
#define CAM_CFG_GLOB_SHIFT_MASK           (0xf << CAM_CFG_GLOB_SHIFT_OFFSET)
#define CAM_CFG_GLOB_SHIFT(val)           (val << CAM_CFG_GLOB_SHIFT_OFFSET)

#define CAM_CFG_GLOB_EN_OFFSET              31
#define CAM_CFG_GLOB_EN_WIDTH               1
#define CAM_CFG_GLOB_EN_MASK              (0x1 << CAM_CFG_GLOB_EN_OFFSET)
#define CAM_CFG_GLOB_EN_ENA               (1 << CAM_CFG_GLOB_EN_OFFSET)
#define CAM_CFG_GLOB_EN_DIS               (0 << CAM_CFG_GLOB_EN_OFFSET)

#define CAM_CFG_LL_FRAMESLICE_LLX_OFFSET    0
#define CAM_CFG_LL_FRAMESLICE_LLX_WIDTH   16
#define CAM_CFG_LL_FRAMESLICE_LLX_MASK    (0xffff << CAM_CFG_LL_FRAMESLICE_LLX_OFFSET)
#define CAM_CFG_LL_FRAMESLICE_LLX(val)    (val << CAM_CFG_LL_FRAMESLICE_LLX_OFFSET)

#define CAM_CFG_LL_FRAMESLICE_LLY_OFFSET    16
#define CAM_CFG_LL_FRAMESLICE_LLY_WIDTH   16
#define CAM_CFG_LL_FRAMESLICE_LLY_MASK    (0xffff << CAM_CFG_LL_FRAMESLICE_LLY_OFFSET)
#define CAM_CFG_LL_FRAMESLICE_LLY(val)    (val << CAM_CFG_LL_FRAMESLICE_LLY_OFFSET)

#define CAM_CFG_UR_FRAMESLICE_URX_OFFSET    0
#define CAM_CFG_UR_FRAMESLICE_URX_WIDTH   16
#define CAM_CFG_UR_FRAMESLICE_URX_MASK    (0xffff << CAM_CFG_UR_FRAMESLICE_URX_OFFSET)
#define CAM_CFG_UR_FRAMESLICE_URX(val)    (val << CAM_CFG_UR_FRAMESLICE_URX_OFFSET)

#define CAM_CFG_UR_FRAMESLICE_URY_OFFSET    16
#define CAM_CFG_UR_FRAMESLICE_URY_WIDTH   16
#define CAM_CFG_UR_FRAMESLICE_URY_MASK    (0xffff << CAM_CFG_UR_FRAMESLICE_URY_OFFSET)
#define CAM_CFG_UR_FRAMESLICE_URY(val)    (val << CAM_CFG_UR_FRAMESLICE_URY_OFFSET)

#define CAM_CFG_SIZE_ROWLEN_OFFSET      16
#define CAM_CFG_SIZE_ROWLEN_WIDTH     16
#define CAM_CFG_SIZE_ROWLEN_MASK    (0xffff << CAM_CFG_SIZE_ROWLEN_OFFSET)
#define CAM_CFG_SIZE_ROWLEN(val)    ((val - 1) << CAM_CFG_SIZE_ROWLEN_OFFSET)

#define CAM_CFG_FILTER_B_COEFF_OFFSET     0
#define CAM_CFG_FILTER_B_COEFF_WIDTH    8
#define CAM_CFG_FILTER_B_COEFF_MASK     (0xff << CAM_CFG_FILTER_B_COEFF_OFFSET)
#define CAM_CFG_FILTER_B_COEFF(val)     (val << CAM_CFG_FILTER_B_COEFF_OFFSET)

#define CAM_CFG_FILTER_G_COEFF_OFFSET     8
#define CAM_CFG_FILTER_G_COEFF_WIDTH    8
#define CAM_CFG_FILTER_G_COEFF_MASK     (0xff << CAM_CFG_FILTER_G_COEFF_OFFSET)
#define CAM_CFG_FILTER_G_COEFF(val)     (val << CAM_CFG_FILTER_G_COEFF_OFFSET)

#define CAM_CFG_FILTER_R_COEFF_OFFSET     16
#define CAM_CFG_FILTER_R_COEFF_WIDTH    8
#define CAM_CFG_FILTER_R_COEFF_MASK     (0xff << CAM_CFG_FILTER_R_COEFF_OFFSET)
#define CAM_CFG_FILTER_R_COEFF(val)     (val << CAM_CFG_FILTER_R_COEFF_OFFSET)

// TODO Add enum definitions of CAM register bitfields

///////////////////////////////////////////////////
// TODO Obsolete : to be removed cause deprecated
#define CAM_CFG_GLOB_FRAMEDROP_EN_BIT   0
#define CAM_CFG_GLOB_FRAMEDROP_VAL_BIT  1
#define CAM_CFG_GLOB_FRAMEDROP_VAL_SIZE 6
#define CAM_CFG_GLOB_FRAMESLICE_EN_BIT  7
#define CAM_CFG_GLOB_FORMAT_BIT         8
#define CAM_CFG_GLOB_FORMAT_SIZE        3
#define CAM_CFG_GLOB_SHIFT_BIT          11
#define CAM_CFG_GLOB_SHIFT_SIZE         4
#define CAM_CFG_GLOB_EN_BIT             31

//+ #define CAM_CFG_GLOB_FORMAT_RGB565      0
//+ #define CAM_CFG_GLOB_FORMAT_RGB555      1
//+ #define CAM_CFG_GLOB_FORMAT_RGB444      2
//+ #define CAM_CFG_GLOB_FORMAT_BYPASS      3

#define CAM_CFG_LL_FRAMESLICE_LLX_BIT   0
#define CAM_CFG_LL_FRAMESLICE_LLX_SIZE  16
#define CAM_CFG_LL_FRAMESLICE_LLY_BIT   16
#define CAM_CFG_LL_FRAMESLICE_LLY_SIZE  16

#define CAM_CFG_UR_FRAMESLICE_URX_BIT   0
#define CAM_CFG_UR_FRAMESLICE_URX_SIZE  16
#define CAM_CFG_UR_FRAMESLICE_URY_BIT   16
#define CAM_CFG_UR_FRAMESLICE_URY_SIZE  16

#define CAM_CFG_SIZE_ROWLEN_BIT  16
#define CAM_CFG_SIZE_ROWLEN_SIZE 16

#define CAM_CFG_FILTER_B_COEFF_BIT  0
#define CAM_CFG_FILTER_B_COEFF_SIZE 8
#define CAM_CFG_FILTER_G_COEFF_BIT  8
#define CAM_CFG_FILTER_G_COEFF_SIZE 8
#define CAM_CFG_FILTER_R_COEFF_BIT  16
#define CAM_CFG_FILTER_R_COEFF_SIZE 8
///////////////////////////////////////////////////

#endif


/*
 * I2S
 */

#ifdef ARCHI_UDMA_HAS_I2S

// I2S custom registers offset definition
#define I2S_EXT_OFFSET             (0x00)
#define I2S_CFG_CLKGEN0_OFFSET            (0x04)
#define I2S_CFG_CLKGEN1_OFFSET            (0x08)
#define I2S_CFG_CLKGEN_OFFSET(clk) (I2S_CFG_CLKGEN0_OFFSET + (clk)*4)
#define I2S_CHMODE_OFFSET          (0x0C)
#define I2S_FILT_CH0_OFFSET        (0x10)
#define I2S_FILT_CH1_OFFSET        (0x14)
#define I2S_FILT_CH_OFFSET(clk)    (I2S_FILT_CH0_OFFSET + (clk)*4)

// I2S custom registers bitfields offset, mask, value definition
#define I2S_EXT_BITS_WORD_OFFSET  0
#define I2S_EXT_BITS_WORD_WIDTH   5
#define I2S_EXT_BITS_WORD_MASK    (0x1f << I2S_EXT_BITS_WORD_OFFSET)
#define I2S_EXT_BITS_WORD(val)    ((val-1) << I2S_EXT_BITS_WORD_OFFSET)


#define I2S_CFG_CLKGEN_BITS_WORD_OFFSET 0
#define I2S_CFG_CLKGEN_BITS_WORD_WIDTH  5
#define I2S_CFG_CLKGEN_BITS_WORD_MASK   (0x1f << I2S_CFG_CLKGEN_BITS_WORD_OFFSET)
#define I2S_CFG_CLKGEN_BITS_WORD(val)   ((val-1) << I2S_CFG_CLKGEN_BITS_WORD_OFFSET)

#define I2S_CFG_CLKGEN_CLK_EN_OFFSET    8
#define I2S_CFG_CLKGEN_CLK_EN_WIDTH   1
#define I2S_CFG_CLKGEN_CLK_EN_MASK    (0x1 << I2S_CFG_CLKGEN_CLK_EN_OFFSET)
#define I2S_CFG_CLKGEN_CLK_EN     (1 << I2S_CFG_CLKGEN_CLK_EN_OFFSET)
#define I2S_CFG_CLKGEN_CLK_DIS    (0 << I2S_CFG_CLKGEN_CLK_EN_OFFSET)

#define I2S_CFG_CLKGEN_CLKDIV_OFFSET    16
#define I2S_CFG_CLKGEN_CLKDIV_WIDTH   16
#define I2S_CFG_CLKGEN_CLKDIV_MASK    (0xffff << I2S_CFG_CLKGEN_CLKDIV_OFFSET)
#define I2S_CFG_CLKGEN_CLKDIV(val)    (val << I2S_CFG_CLKGEN_CLKDIV_OFFSET)


#define I2S_CFG_CLKGEN0_BITS_WORD_OFFSET  0
#define I2S_CFG_CLKGEN0_BITS_WORD_WIDTH 5
#define I2S_CFG_CLKGEN0_BITS_WORD_MASK    (0x1f << I2S_CFG_CLKGEN0_BITS_WORD_OFFSET)
#define I2S_CFG_CLKGEN0_BITS_WORD(val)    ((val-1) << I2S_CFG_CLKGEN0_BITS_WORD_OFFSET)

#define I2S_CFG_CLKGEN0_CLK_EN_OFFSET   8
#define I2S_CFG_CLKGEN0_CLK_EN_WIDTH    1
#define I2S_CFG_CLKGEN0_CLK_EN_MASK   (0x1 << I2S_CFG_CLKGEN0_CLK_EN_OFFSET)
#define I2S_CFG_CLKGEN0_CLK_EN      (1 << I2S_CFG_CLKGEN0_CLK_EN_OFFSET)
#define I2S_CFG_CLKGEN0_CLK_DIS   (0 << I2S_CFG_CLKGEN0_CLK_EN_OFFSET)

#define I2S_CFG_CLKGEN0_CLKDIV_OFFSET   16
#define I2S_CFG_CLKGEN0_CLKDIV_WIDTH    16
#define I2S_CFG_CLKGEN0_CLKDIV_MASK   (0xffff << I2S_CFG_CLKGEN0_CLKDIV_OFFSET)
#define I2S_CFG_CLKGEN0_CLKDIV(val)   (val << I2S_CFG_CLKGEN0_CLKDIV_OFFSET)

#define I2S_CFG_CLKGEN1_BITS_WORD_OFFSET  0
#define I2S_CFG_CLKGEN1_BITS_WORD_WIDTH 5
#define I2S_CFG_CLKGEN1_BITS_WORD_MASK    (0x1f << I2S_CFG_CLKGEN1_BITS_WORD_OFFSET)
#define I2S_CFG_CLKGEN1_BITS_WORD(val)    ((val-1) << I2S_CFG_CLKGEN1_BITS_WORD_OFFSET)

#define I2S_CFG_CLKGEN1_CLK_EN_OFFSET   8
#define I2S_CFG_CLKGEN1_CLK_EN_WIDTH    1
#define I2S_CFG_CLKGEN1_CLK_EN_MASK   (0x1 << I2S_CFG_CLKGEN1_CLK_EN_OFFSET)
#define I2S_CFG_CLKGEN1_CLK_EN      (1 << I2S_CFG_CLKGEN1_CLK_EN_OFFSET)
#define I2S_CFG_CLKGEN1_CLK_DIS   (0 << I2S_CFG_CLKGEN1_CLK_EN_OFFSET)

#define I2S_CFG_CLKGEN1_CLKDIV_OFFSET   16
#define I2S_CFG_CLKGEN1_CLKDIV_WIDTH    16
#define I2S_CFG_CLKGEN1_CLKDIV_MASK   (0xffff << I2S_CFG_CLKGEN1_CLKDIV_OFFSET)
#define I2S_CFG_CLKGEN1_CLKDIV(val)   (val << I2S_CFG_CLKGEN1_CLKDIV_OFFSET)



#define I2S_CHMODE_CH_SNAPCAM_OFFSET(x)       (0 + (x))
#define I2S_CHMODE_CH_SNAPCAM_WIDTH(x)        (1)
#define I2S_CHMODE_CH_SNAPCAM_MASK(x)         (0x1 << I2S_CHMODE_CH_SNAPCAM_OFFSET(x))
#define I2S_CHMODE_CH_SNAPCAM_ENA(x)          (0x1 << I2S_CHMODE_CH_SNAPCAM_OFFSET(x))
#define I2S_CHMODE_CH_SNAPCAM_DIS(x)          (0x0 << I2S_CHMODE_CH_SNAPCAM_OFFSET(x))

#define I2S_CHMODE_CH_LSBFIRST_OFFSET(x)      (4 + (x))
#define I2S_CHMODE_CH_LSBFIRST_WIDTH(x)       (1)
#define I2S_CHMODE_CH_LSBFIRST_MASK(x)        (0x1 << I2S_CHMODE_CH_LSBFIRST_OFFSET(x))
#define I2S_CHMODE_CH_LSBFIRST_ENA(x)         (1 << I2S_CHMODE_CH_LSBFIRST_OFFSET(x))
#define I2S_CHMODE_CH_LSBFIRST_DIS(x)         (0 << I2S_CHMODE_CH_LSBFIRST_OFFSET(x))

#define I2S_CHMODE_CH_PDM_USEFILTER_OFFSET(x) (8 + (x))
#define I2S_CHMODE_CH_PDM_USEFILTER_WIDTH(x)  (1)
#define I2S_CHMODE_CH_PDM_USEFILTER_MASK(x)   (0x1 << I2S_CHMODE_CH_PDM_USEFILTER_OFFSET(x))
#define I2S_CHMODE_CH_PDM_USEFILTER_ENA(x)    (1 << I2S_CHMODE_CH_PDM_USEFILTER_OFFSET(x))
#define I2S_CHMODE_CH_PDM_USEFILTER_DIS(x)    (0 << I2S_CHMODE_CH_PDM_USEFILTER_OFFSET(x))

#define I2S_CHMODE_CH_PDM_EN_OFFSET(x)        (12 + (x))
#define I2S_CHMODE_CH_PDM_EN_WIDTH(x)         (1)
#define I2S_CHMODE_CH_PDM_EN_MASK(x)          (0x1 << I2S_CHMODE_CH_PDM_EN_OFFSET(x))
#define I2S_CHMODE_CH_PDM_EN_ENA(x)           (1 << I2S_CHMODE_CH_PDM_EN_OFFSET(x))
#define I2S_CHMODE_CH_PDM_EN_DIS(x)           (0 << I2S_CHMODE_CH_PDM_EN_OFFSET(x))

#define I2S_CHMODE_CH_USEDDR_OFFSET(x)        (16 + (x))
#define I2S_CHMODE_CH_USEDDR_WIDTH(x)         (1)
#define I2S_CHMODE_CH_USEDDR_MASK(x)          (0x1 << I2S_CHMODE_CH_USEDDR_OFFSET(x))
#define I2S_CHMODE_CH_USEDDR_ENA(x)           (1 << I2S_CHMODE_CH_USEDDR_OFFSET(x))
#define I2S_CHMODE_CH_USEDDR_DIS(x)           (0 << I2S_CHMODE_CH_USEDDR_OFFSET(x))

#define I2S_CHMODE_CH_MODE_OFFSET(x)          (24 + (x*2))
#define I2S_CHMODE_CH_MODE_WIDTH(x)           (2)
#define I2S_CHMODE_CH_MODE_MASK(x)            (0x3 << I2S_CHMODE_CH_MODE_OFFSET(x))
#define I2S_CHMODE_CH_MODE_CLK(x,clk)         (clk << I2S_CHMODE_CH_MODE_OFFSET(x))
#define I2S_CHMODE_CH_MODE_EXTCLK_INTWS(x)    (2 << I2S_CHMODE_CH_MODE_OFFSET(x))
#define I2S_CHMODE_CH_MODE_EXTCLK_EXTWS(x)    (2 << I2S_CHMODE_CH_MODE_OFFSET(x))



#define I2S_CHMODE_CH0_SNAPCAM_OFFSET 0
#define I2S_CHMODE_CH0_SNAPCAM_WIDTH  1
#define I2S_CHMODE_CH0_SNAPCAM_MASK (0x1 << I2S_CHMODE_CH0_SNAPCAM_OFFSET)
#define I2S_CHMODE_CH0_SNAPCAM_ENA  (0x1 << I2S_CHMODE_CH0_SNAPCAM_OFFSET)
#define I2S_CHMODE_CH0_SNAPCAM_DIS  (0x0 << I2S_CHMODE_CH0_SNAPCAM_OFFSET)

#define I2S_CHMODE_CH0_LSBFIRST_OFFSET  4
#define I2S_CHMODE_CH0_LSBFIRST_WIDTH 1
#define I2S_CHMODE_CH0_LSBFIRST_MASK  (0x1 << I2S_CHMODE_CH0_LSBFIRST_OFFSET)
#define I2S_CHMODE_CH0_LSBFIRST_ENA (1 << I2S_CHMODE_CH0_LSBFIRST_OFFSET)
#define I2S_CHMODE_CH0_LSBFIRST_DIS (0 << I2S_CHMODE_CH0_LSBFIRST_OFFSET)

#define I2S_CHMODE_CH0_PDM_USEFILTER_OFFSET   8
#define I2S_CHMODE_CH0_PDM_USEFILTER_WIDTH    1
#define I2S_CHMODE_CH0_PDM_USEFILTER_MASK   (0x1 << I2S_CHMODE_CH0_PDM_USEFILTER_OFFSET)
#define I2S_CHMODE_CH0_PDM_USEFILTER_ENA    (1 << I2S_CHMODE_CH0_PDM_USEFILTER_OFFSET)
#define I2S_CHMODE_CH0_PDM_USEFILTER_DIS    (0 << I2S_CHMODE_CH0_PDM_USEFILTER_OFFSET)

#define I2S_CHMODE_CH0_PDM_EN_OFFSET  12
#define I2S_CHMODE_CH0_PDM_EN_WIDTH 1
#define I2S_CHMODE_CH0_PDM_EN_MASK  (0x1 << I2S_CHMODE_CH0_PDM_EN_OFFSET)
#define I2S_CHMODE_CH0_PDM_EN_ENA (1 << I2S_CHMODE_CH0_PDM_EN_OFFSET)
#define I2S_CHMODE_CH0_PDM_EN_DIS (0 << I2S_CHMODE_CH0_PDM_EN_OFFSET)

#define I2S_CHMODE_CH0_USEDDR_OFFSET  16
#define I2S_CHMODE_CH0_USEDDR_WIDTH 1
#define I2S_CHMODE_CH0_USEDDR_MASK  (0x1 << I2S_CHMODE_CH0_USEDDR_OFFSET)
#define I2S_CHMODE_CH0_USEDDR_ENA (1 << I2S_CHMODE_CH0_USEDDR_OFFSET)
#define I2S_CHMODE_CH0_USEDDR_DIS (0 << I2S_CHMODE_CH0_USEDDR_OFFSET)

#define I2S_CHMODE_CH0_MODE_OFFSET    24
#define I2S_CHMODE_CH0_MODE_WIDTH   2
#define I2S_CHMODE_CH0_MODE_MASK    (0x3 << I2S_CHMODE_CH0_MODE_OFFSET)
#define I2S_CHMODE_CH0_MODE_CLK0    (0 << I2S_CHMODE_CH0_MODE_OFFSET)
#define I2S_CHMODE_CH0_MODE_CLK1    (1 << I2S_CHMODE_CH0_MODE_OFFSET)
#define I2S_CHMODE_CH0_MODE_EXTCLK_INTWS  (2 << I2S_CHMODE_CH0_MODE_OFFSET)
#define I2S_CHMODE_CH0_MODE_EXTCLK_EXTWS  (2 << I2S_CHMODE_CH0_MODE_OFFSET)

#define I2S_CHMODE_CH1_SNAPCAM_OFFSET 1
#define I2S_CHMODE_CH1_SNAPCAM_WIDTH  1
#define I2S_CHMODE_CH1_SNAPCAM_MASK (0x1 << I2S_CHMODE_CH1_SNAPCAM_OFFSET)
#define I2S_CHMODE_CH1_SNAPCAM_ENA  (0x1 << I2S_CHMODE_CH1_SNAPCAM_OFFSET)
#define I2S_CHMODE_CH1_SNAPCAM_DIS  (0x0 << I2S_CHMODE_CH1_SNAPCAM_OFFSET)

#define I2S_CHMODE_CH1_LSBFIRST_OFFSET  5
#define I2S_CHMODE_CH1_LSBFIRST_WIDTH 1
#define I2S_CHMODE_CH1_LSBFIRST_MASK  (0x1 << I2S_CHMODE_CH1_LSBFIRST_OFFSET)
#define I2S_CHMODE_CH1_LSBFIRST_ENA (1 << I2S_CHMODE_CH1_LSBFIRST_OFFSET)
#define I2S_CHMODE_CH1_LSBFIRST_DIS (0 << I2S_CHMODE_CH1_LSBFIRST_OFFSET)

#define I2S_CHMODE_CH1_PDM_USEFILTER_OFFSET 9
#define I2S_CHMODE_CH1_PDM_USEFILTER_WIDTH  1
#define I2S_CHMODE_CH1_PDM_USEFILTER_MASK (0x1 << I2S_CHMODE_CH1_PDM_USEFILTER_OFFSET)
#define I2S_CHMODE_CH1_PDM_USEFILTER_ENA  (1 << I2S_CHMODE_CH1_PDM_USEFILTER_OFFSET)
#define I2S_CHMODE_CH1_PDM_USEFILTER_DIS  (0 << I2S_CHMODE_CH1_PDM_USEFILTER_OFFSET)

#define I2S_CHMODE_CH1_PDM_EN_OFFSET  13
#define I2S_CHMODE_CH1_PDM_EN_WIDTH 1
#define I2S_CHMODE_CH1_PDM_EN_MASK  (0x1 << I2S_CHMODE_CH1_PDM_EN_OFFSET)
#define I2S_CHMODE_CH1_PDM_EN_ENA (1 << I2S_CHMODE_CH1_PDM_EN_OFFSET)
#define I2S_CHMODE_CH1_PDM_EN_DIS (0 << I2S_CHMODE_CH1_PDM_EN_OFFSET)

#define I2S_CHMODE_CH1_USEDDR_OFFSET  17
#define I2S_CHMODE_CH1_USEDDR_WIDTH 1
#define I2S_CHMODE_CH1_USEDDR_MASK  (0x1 << I2S_CHMODE_CH1_USEDDR_OFFSET)
#define I2S_CHMODE_CH1_USEDDR_ENA (1 << I2S_CHMODE_CH1_USEDDR_OFFSET)
#define I2S_CHMODE_CH1_USEDDR_DIS (0 << I2S_CHMODE_CH1_USEDDR_OFFSET)

#define I2S_CHMODE_CH1_MODE_OFFSET    26
#define I2S_CHMODE_CH1_MODE_WIDTH   2
#define I2S_CHMODE_CH1_MODE_MASK    (0x3 << I2S_CHMODE_CH1_MODE_OFFSET)
#define I2S_CHMODE_CH1_MODE_CLK0    (0 << I2S_CHMODE_CH1_MODE_OFFSET)
#define I2S_CHMODE_CH1_MODE_CLK1    (1 << I2S_CHMODE_CH1_MODE_OFFSET)
#define I2S_CHMODE_CH1_MODE_EXTCLK_INTWS  (2 << I2S_CHMODE_CH1_MODE_OFFSET)
#define I2S_CHMODE_CH1_MODE_EXTCLK_EXTWS  (2 << I2S_CHMODE_CH1_MODE_OFFSET)

// Channel clock modes
// Write strobe is the clock for switching left/right channels
#define I2S_CHMODE_INT_CLOCK0        0    // Internal clock 0
#define I2S_CHMODE_INT_CLOCK1        1    // Internal clock 1
#define I2S_CHMODE_EXT_CLOCK_INT_WS  2    // External clock internal write strobe
#define I2S_CHMODE_EXT_CLOCK_EXT_WS  3    // External clock external write strobe


#define I2S_FILT_CH0_DECIMATION_OFFSET  0
#define I2S_FILT_CH0_DECIMATION_WIDTH 10
#define I2S_FILT_CH0_DECIMATION_MASK  (0x3ff << I2S_FILT_CH0_DECIMATION_OFFSET)
#define I2S_FILT_CH0_DECIMATION(val)  (val << I2S_FILT_CH0_DECIMATION_OFFSET)

#define I2S_FILT_CH0_SHIFT_OFFSET 16
#define I2S_FILT_CH0_SHIFT_WIDTH  3
#define I2S_FILT_CH0_SHIFT_MASK   (0x7 << I2S_FILT_CH0_SHIFT_OFFSET)
#define I2S_FILT_CH0_SHIFT(val)   (val << I2S_FILT_CH0_SHIFT_OFFSET)

#define I2S_FILT_CH1_DECIMATION_OFFSET  0
#define I2S_FILT_CH1_DECIMATION_WIDTH 10
#define I2S_FILT_CH1_DECIMATION_MASK  (0x3ff << I2S_FILT_CH1_DECIMATION_OFFSET)
#define I2S_FILT_CH1_DECIMATION(val)  (val << I2S_FILT_CH1_DECIMATION_OFFSET)

#define I2S_FILT_CH1_SHIFT_OFFSET 16
#define I2S_FILT_CH1_SHIFT_WIDTH  3
#define I2S_FILT_CH1_SHIFT_MASK   (0x7 << I2S_FILT_CH1_SHIFT_OFFSET)
#define I2S_FILT_CH1_SHIFT(val)   (val << I2S_FILT_CH1_SHIFT_OFFSET)
///////////////////////////////////////////////////

#endif


/*
 * UART
 */

#ifdef ARCHI_UDMA_HAS_UART

// UART custom registers offset definition
#define UART_STATUS_OFFSET               (0x00)
#define UART_SETUP_OFFSET                (0x04)

// UART custom registers bitfields offset, mask, value definition
// STATUS
#define UART_TX_BUSY_OFFSET   0
#define UART_TX_BUSY_WIDTH    1
#define UART_TX_BUSY_MASK   (0x1 << UART_TX_BUSY_OFFSET)
#define UART_TX_BUSY      (0x1 << UART_TX_BUSY_OFFSET)

#define UART_RX_BUSY_OFFSET   1
#define UART_RX_BUSY_WIDTH    1
#define UART_RX_BUSY_MASK   (0x1 << UART_RX_BUSY_OFFSET)
#define UART_RX_BUSY      (0x1 << UART_RX_BUSY_OFFSET)

#define UART_RX_PE_OFFSET   2
#define UART_RX_PE_WIDTH    1
#define UART_RX_PE_MASK     (0x1 << UART_RX_PE_OFFSET)
#define UART_RX_PE      (0x1 << UART_RX_PE_OFFSET)

// SETUP
#define UART_PARITY_OFFSET    0
#define UART_PARITY_WIDTH   1
#define UART_PARITY_MASK    (0x1 << UART_PARITY_OFFSET)
#define UART_PARITY_DIS     (0 << UART_PARITY_OFFSET)
#define UART_PARITY_ENA     (1 << UART_PARITY_OFFSET)

#define UART_BIT_LENGTH_OFFSET    1
#define UART_BIT_LENGTH_WIDTH   2
#define UART_BIT_LENGTH_MASK    (0x3 << UART_BIT_LENGTH_OFFSET)
#define UART_BIT_LENGTH_5   (0 << UART_BIT_LENGTH_OFFSET)
#define UART_BIT_LENGTH_6   (1 << UART_BIT_LENGTH_OFFSET)
#define UART_BIT_LENGTH_7   (2 << UART_BIT_LENGTH_OFFSET)
#define UART_BIT_LENGTH_8   (3 << UART_BIT_LENGTH_OFFSET)

#define UART_STOP_BITS_OFFSET   3
#define UART_STOP_BITS_WIDTH    1
#define UART_STOP_BITS_MASK   (0x1 << UART_STOP_BITS_OFFSET)
#define UART_STOP_BITS_1    (0 << UART_STOP_BITS_OFFSET)
#define UART_STOP_BITS_2    (1 << UART_STOP_BITS_OFFSET)

#define UART_TX_OFFSET    8
#define UART_TX_WIDTH   1
#define UART_TX_MASK    (0x1 << UART_TX_OFFSET)
#define UART_TX_DIS   (0 << UART_TX_OFFSET)
#define UART_TX_ENA   (1 << UART_TX_OFFSET)

#define UART_RX_OFFSET    9
#define UART_RX_WIDTH   1
#define UART_RX_MASK    (0x1 << UART_RX_OFFSET)
#define UART_RX_DIS   (0 << UART_RX_OFFSET)
#define UART_RX_ENA   (1 << UART_RX_OFFSET)

#define UART_CLKDIV_OFFSET    16
#define UART_CLKDIV_WIDTH   16
#define UART_CLKDIV_MASK    (0xffff << UART_CLKDIV_OFFSET)
#define UART_CLKDIV(val)    (val << UART_CLKDIV_OFFSET)

#endif




/*
 * I2C
 */

#ifdef ARCHI_UDMA_HAS_I2C

// I2C command IDS definition
#define I2C_CMD_OFFSET       4
#define I2C_CMD_START                    (0x0 << I2C_CMD_OFFSET)
#define I2C_CMD_STOP                     (0x2 << I2C_CMD_OFFSET)
#define I2C_CMD_RD_ACK                   (0x4 << I2C_CMD_OFFSET)
#define I2C_CMD_RD_NACK                  (0x6 << I2C_CMD_OFFSET)
#define I2C_CMD_WR                       (0x8 << I2C_CMD_OFFSET)
#define I2C_CMD_WAIT                     (0xA << I2C_CMD_OFFSET)
#define I2C_CMD_RPT                      (0xC << I2C_CMD_OFFSET)
#define I2C_CMD_CFG                      (0xE << I2C_CMD_OFFSET)
#define I2C_CMD_WAIT_EV                  (0x1 << I2C_CMD_OFFSET)

#endif


/*
 * SPIM
 */

#ifdef ARCHI_UDMA_HAS_SPIM

#define ARCHI_SPIM_CMD_OFFSET      0x20


// SPI commands IDS definition
#define SPI_CMD_CFG_ID       0
#define SPI_CMD_SOT_ID       1
#define SPI_CMD_SEND_CMD_ID  2
#define SPI_CMD_SEND_ADDR_ID 3
#define SPI_CMD_DUMMY_ID     4
#define SPI_CMD_WAIT_ID      5
#define SPI_CMD_TX_DATA_ID   6
#define SPI_CMD_RX_DATA_ID   7
#define SPI_CMD_RPT_ID       8
#define SPI_CMD_EOT_ID       9
#define SPI_CMD_RPT_END_ID   10
#define SPI_CMD_RX_CHECK_ID  11
#define SPI_CMD_FUL_ID       12

// SPI command fields offset, mask, value definition
// SPI commands fields offsets
#define SPI_CMD_ID_OFFSET       28

// COMMON definitions
#define SPI_CMD_QPI_ENA   1
#define SPI_CMD_QPI_DIS   0
#define SPI_CMD_LSB_FIRST  1
#define SPI_CMD_MSB_FIRST  0
#define SPI_CMD_4_WORD_PER_TRANSF 2
#define SPI_CMD_2_WORD_PER_TRANSF 1
#define SPI_CMD_1_WORD_PER_TRANSF 0
#define SPI_CMD_DATA_WITDH(val) (val)
#define SPI_CMD_CMD_SIZE(val) (val)

// CFG
#define SPI_CMD_CFG_CLK_DIV_OFFSET      0
#define SPI_CMD_CFG_CLK_DIV_WIDTH   8
#define SPI_CMD_CFG_CPHA_OFFSET         8
#define SPI_CMD_CFG_CPOL_OFFSET       9

#define SPI_CMD_CFG_CLKDIV(val) (val)
#define SPI_CMD_CFG_CPOL_POS  1
#define SPI_CMD_CFG_CPOL_NEG  0
#define SPI_CMD_CFG_CPHA_STD  1
#define SPI_CMD_CFG_CPHA_OPP  0

// SOT
#define SPI_CMD_SOT_CS_OFFSET    0
#define SPI_CMD_SOT_CS_WIDTH     2

#define SPI_CMD_SOT_CS0   0
#define SPI_CMD_SOT_CS1   1
#define SPI_CMD_SOT_CS2   2
#define SPI_CMD_SOT_CS3   3

// SEND_CMD
#define SPI_CMD_SEND_CMD_CMD_OFFSET   0
#define SPI_CMD_SEND_CMD_CMD_WIDTH    16
#define SPI_CMD_SEND_CMD_SIZE_OFFSET  16
#define SPI_CMD_SEND_CMD_SIZE_WIDTH   4
#define SPI_CMD_SEND_CMD_QPI_OFFSET   27

// SEND_ADDR
#define SPI_CMD_SEND_ADDR_SIZE_OFFSET   16
#define SPI_CMD_SEND_ADDR_SIZE_WIDTH     5
#define SPI_CMD_SEND_ADDR_QPI_OFFSET    27

//#define SPI_CMD_SEND_ADDR_VALUE(value)  ((((value) & 0xff000000) >> 24) | (((value) & 0xff0000) >> 8) | (((value) & 0xff00) << 8) | (((value) & 0xff) << 24))
#define SPI_CMD_SEND_ADDR_VALUE(value)  (value)


// SEND_DUMMY
#define SPI_CMD_DUMMY_CYCLE_OFFSET      16
#define SPI_CMD_DUMMY_CYCLE_WIDTH        5

// TX_DATA
#define SPI_CMD_TX_DATA_SIZE_OFFSET          0
#define SPI_CMD_TX_DATA_SIZE_WIDTH          16
#define SPI_CMD_TX_DATA_BYTE_ALIGN_OFFSET   26
#define SPI_CMD_TX_DATA_QPI_OFFSET          27

// RX_DATA
#define SPI_CMD_RX_DATA_SIZE_OFFSET          0
#define SPI_CMD_RX_DATA_SIZE_WIDTH          16
#define SPI_CMD_RX_DATA_BYTE_ALIGN_OFFSET   26
#define SPI_CMD_RX_DATA_QPI_OFFSET          27

// RPT
#define SPI_CMD_RPT_NB_OFFSET                0
#define SPI_CMD_RPT_NB_WIDTH                16

// EOT
#define SPI_CMD_EOT_GEN_EVT_OFFSET           0

#define SPI_CMD_EOT_EVENT_ENA                1
#define SPI_CMD_EOT_EVENT_DIS                0

// WAIT
#define SPI_CMD_WAIT_EVENT_OFFSET            0
#define SPI_CMD_WAIT_EVENT_WIDTH             2

// RX_CHECK
#define SPI_CMD_RX_CHECK_VALUE_OFFSET        0
#define SPI_CMD_RX_CHECK_VALUE_WIDTH        16

#define SPI_CMD_RX_CHECK_SIZE_OFFSET        16
#define SPI_CMD_RX_CHECK_SIZE_WIDTH          4

#define SPI_CMD_RX_CHECK_MODE_OFFSET        24
#define SPI_CMD_RX_CHECK_MODE_WIDTH          2

#define SPI_CMD_RX_CHECK_BYTE_ALIGN_OFFSET  26

#define SPI_CMD_RX_CHECK_QPI_OFFSET         27

#define SPI_CMD_RX_CHECK_MODE_MATCH          0
#define SPI_CMD_RX_CHECK_MODE_ONES           1
#define SPI_CMD_RX_CHECK_MODE_ZEROS          2
#define SPI_CMD_RX_CHECK_MODE_MASK           3

// FULL DUPLEX
#define SPI_CMD_FUL_SIZE_OFFSET              0
#define SPI_CMD_FUL_SIZE_WIDTH              16
#define SPI_CMD_FUL_WORDTRANS_OFFSET 21
#define SPI_CMD_FUL_LSBFIRST_OFFSET 26
#define SPI_CMD_FUL_BITSWORD_OFFSET 16

#define SPI_CMD_SETUP_UC_TXRXEN_OFFSET 27
#define SPI_CMD_SETUP_UC_DS_OFFSET     25

#define SPI_CMD_TX_DATA_WORDTRANS_OFFSET 21
#define SPI_CMD_TX_DATA_LSBFIRST_OFFSET 26
#define SPI_CMD_TX_DATA_BITSWORD_OFFSET 16

#define SPI_CMD_RX_DATA_WORDTRANS_OFFSET 21
#define SPI_CMD_RX_DATA_LSBFIRST_OFFSET 26
#define SPI_CMD_RX_DATA_BITSWORD_OFFSET 16

// SPI CMD encoding
#define SPI_CMD_CFG(clockDiv,cpol,cpha)                         ((SPI_CMD_CFG_ID<<SPI_CMD_ID_OFFSET)       | ((cpol)<<SPI_CMD_CFG_CPOL_OFFSET)          | ((cpha)<<SPI_CMD_CFG_CPHA_OFFSET)                | ((clockDiv)<<SPI_CMD_CFG_CLK_DIV_OFFSET))
#define SPI_CMD_SOT(cs)                                         ((SPI_CMD_SOT_ID << SPI_CMD_ID_OFFSET)     | ((cs) << SPI_CMD_SOT_CS_OFFSET))
#define SPI_CMD_SEND_CMD(cmd,bits,qpi)                          ((SPI_CMD_SEND_CMD_ID<<SPI_CMD_ID_OFFSET)  | ((qpi)<<SPI_CMD_SEND_CMD_QPI_OFFSET)       | (((bits)-1)<<SPI_CMD_SEND_CMD_SIZE_OFFSET)       | (cmd&0xFFFF) )
#define SPI_CMD_SEND_BITS(data,bits,qpi)                        ((SPI_CMD_SEND_CMD_ID<<SPI_CMD_ID_OFFSET)  | ((qpi)<<SPI_CMD_SEND_CMD_QPI_OFFSET)       | (((bits)-1)<<SPI_CMD_SEND_CMD_SIZE_OFFSET)       | (data&0xFFFF) )
#define SPI_CMD_DUMMY(cycles)                                   ((SPI_CMD_DUMMY_ID<<SPI_CMD_ID_OFFSET)     | (((cycles)-1)<<SPI_CMD_DUMMY_CYCLE_OFFSET))
#define SPI_CMD_SETUP_UCA(txrxen,ds,addr)                       ((SPI_CMD_SETUP_UCA_ID<<SPI_CMD_ID_OFFSET) | ((txrxen)<<SPI_CMD_SETUP_UC_TXRXEN_OFFSET) | ((int)addr & 0xFFFFF))
#define SPI_CMD_SETUP_UCS(txrxen,ds,size)                       ((SPI_CMD_SETUP_UCS_ID<<SPI_CMD_ID_OFFSET) | ((txrxen)<<SPI_CMD_SETUP_UC_TXRXEN_OFFSET) | ((ds)<<SPI_CMD_SETUP_UC_DS_OFFSET)               | (size & 0xFFFF))
#define SPI_CMD_TX_DATA(words,wordstrans,bitsword,qpi,lsbfirst) ((SPI_CMD_TX_DATA_ID<<SPI_CMD_ID_OFFSET)   | ((qpi)<<SPI_CMD_TX_DATA_QPI_OFFSET)        | ((wordstrans)<<SPI_CMD_TX_DATA_WORDTRANS_OFFSET) | ((bitsword-1)<<SPI_CMD_TX_DATA_BITSWORD_OFFSET) | (((words)-1) << SPI_CMD_TX_DATA_SIZE_OFFSET) | ((lsbfirst)<<SPI_CMD_TX_DATA_LSBFIRST_OFFSET))
#define SPI_CMD_RX_DATA(words,wordstrans,bitsword,qpi,lsbfirst) ((SPI_CMD_RX_DATA_ID<<SPI_CMD_ID_OFFSET)   | ((qpi)<<SPI_CMD_RX_DATA_QPI_OFFSET)        | ((wordstrans)<<SPI_CMD_RX_DATA_WORDTRANS_OFFSET) | ((bitsword-1)<<SPI_CMD_RX_DATA_BITSWORD_OFFSET) | (((words)-1) << SPI_CMD_RX_DATA_SIZE_OFFSET) | ((lsbfirst)<<SPI_CMD_RX_DATA_LSBFIRST_OFFSET))
#define SPI_CMD_RPT(iter)                                       ((SPI_CMD_RPT_ID<<SPI_CMD_ID_OFFSET)       | ((iter)<<SPI_CMD_RPT_NB_OFFSET))
#define SPI_CMD_EOT(evt)                                        ((SPI_CMD_EOT_ID<<SPI_CMD_ID_OFFSET)       | ((evt)<<SPI_CMD_EOT_GEN_EVT_OFFSET))

#define SPI_CMD_RX_CHECK(mode,bits,value,qpi,byte_align) \
  ((SPI_CMD_RX_CHECK_ID<<SPI_CMD_ID_OFFSET) | \
  ((value) << SPI_CMD_RX_CHECK_VALUE_OFFSET) | \
  ((mode) << SPI_CMD_RX_CHECK_MODE_OFFSET) | \
  (((bits)-1) << SPI_CMD_RX_CHECK_SIZE_OFFSET) | \
  ((byte_align)<<SPI_CMD_RX_CHECK_BYTE_ALIGN_OFFSET) | \
  ((qpi)<<SPI_CMD_RX_CHECK_QPI_OFFSET))

#define SPI_CMD_WAIT(event)               ((SPI_CMD_WAIT_ID<<SPI_CMD_ID_OFFSET) | ((event) << SPI_CMD_WAIT_EVENT_OFFSET))
#define SPI_CMD_RPT_END()                 ((SPI_CMD_RPT_END_ID<<SPI_CMD_ID_OFFSET))
#define SPI_CMD_FUL(words,wordstrans,bitsword,lsbfirst) ((SPI_CMD_FUL_ID<<SPI_CMD_ID_OFFSET)   | ((wordstrans)<<SPI_CMD_FUL_WORDTRANS_OFFSET) | ((bitsword-1)<<SPI_CMD_FUL_BITSWORD_OFFSET) | (((words)-1) << SPI_CMD_FUL_SIZE_OFFSET) | ((lsbfirst)<<SPI_CMD_FUL_LSBFIRST_OFFSET))

#endif


#ifdef ARCHI_UDMA_HAS_HYPER
#include "archi/udma/hyper.h"
#endif

#endif
