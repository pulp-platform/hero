#define SIZE           16
#define MAT_SIZE       (SIZE*SIZE*sizeof(int))

int A_init[SIZE][SIZE]  = {
    {256,2,3,253,252,6,7,249,248,10,11,245,244,14,15,241},
    {17,239,238,20,21,235,234,24,25,231,230,28,29,227,226,32},
    {33,223,222,36,37,219,218,40,41,215,214,44,45,211,210,48},
    {208,50,51,205,204,54,55,201,200,58,59,197,196,62,63,193},
    {192,66,67,189,188,70,71,185,184,74,75,181,180,78,79,177},
    {81,175,174,84,85,171,170,88,89,167,166,92,93,163,162,96},
    {97,159,158,100,101,155,154,104,105,151,150,108,109,147,146,112},
    {144,114,115,141,140,118,119,137,136,122,123,133,132,126,127,129},
    {128,130,131,125,124,134,135,121,120,138,139,117,116,142,143,113},
    {145,111,110,148,149,107,106,152,153,103,102,156,157,99,98,160},
    {161,95,94,164,165,91,90,168,169,87,86,172,173,83,82,176},
    {80,178,179,77,76,182,183,73,72,186,187,69,68,190,191,65},
    {64,194,195,61,60,198,199,57,56,202,203,53,52,206,207,49},
    {209,47,46,212,213,43,42,216,217,39,38,220,221,35,34,224},
    {225,31,30,228,229,27,26,232,233,23,22,236,237,19,18,240},
    {16,242,243,13,12,246,247,9,8,250,251,5,4,254,255,1} 
};

int B_init[SIZE][SIZE]  = {
    {1,0,0,1,0,0,0,0,0,0,0,0,0,0,0,0},
    {0,0,0,0,0,0,1,0,0,0,0,0,0,0,0,0},
    {1,1,1,0,0,0,1,0,1,0,0,0,0,1,0,1},
    {0,0,0,0,0,0,0,0,0,0,0,1,1,0,0,1},
    {0,0,0,0,1,0,0,0,0,0,0,1,0,0,0,0},
    {1,0,0,0,0,0,1,0,0,0,0,0,0,0,0,0},
    {0,0,0,0,0,0,0,0,0,0,1,0,0,0,0,0},
    {0,0,0,0,0,0,0,0,0,0,0,0,0,1,0,0},
    {0,0,0,0,0,0,0,1,0,0,0,0,0,1,0,0},
    {0,0,0,0,1,0,0,0,0,0,0,0,0,0,1,1},
    {0,0,1,1,0,0,0,0,0,0,1,1,0,1,0,0},
    {1,1,0,0,0,0,0,0,0,0,0,0,0,0,1,1},
    {0,0,0,1,0,0,0,1,1,0,0,1,0,1,1,0},
    {0,1,0,0,0,0,0,0,1,0,0,0,0,0,0,0},
    {0,0,0,0,0,0,0,0,0,0,0,0,0,0,1,0},
    {0,1,0,0,0,0,0,0,0,0,0,0,0,0,0,0}
};


