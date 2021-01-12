#include "./nnue/nnue.h"
#include "nnueEval.h"

void initNNUE(char* filename)
{
    nnue_init(filename);
}

int evaluateNNUE(int player, int* pieces, int* squares)
{
    return nnue_evaluate(player, pieces, squares);
}

int evaluateFenNNUE(char* fen)
{
    return nnue_evaluate_fen(fen);
}