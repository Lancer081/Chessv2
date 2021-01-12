#include <iostream>
#include <string>
#include <string.h>
#include <unistd.h>
#include <sys/time.h>
#include <map>
#include "nnueEval.h"

using namespace std;

#define startPosition "rnbqkbnr/pppppppp/8/8/8/8/PPPPPPPP/RNBQKBNR w KQkq - 0 1 "
#define trickyPosition "r3k2r/p1ppqpb1/bn2pnp1/3PN3/1p2P3/2N2Q1p/PPPBBPPP/R3K2R w KQkq - 0 1 "
#define killerPosition "rnbqkb1r/pp1p1pPp/8/2p1pP2/1P1P4/3P3P/P1P1P3/RNBQKBNR w KQkq e6 0 1"

#define setBit(bitboard, bit) (bitboard |= (1ULL << bit))
#define zeroBit(bitboard, bit) (bitboard &= ~(1ULL << bit))
#define getBit(bitboard, bit) ((bitboard >> bit) & 1ULL)

#define encodeMove(source, target, piece, promoted, capture, doublePawn, enpassant, castling) \
    (source) |          \
    (target << 6) |     \
    (piece << 12) |     \
    (promoted << 16) |  \
    (capture << 20) |   \
    (doublePawn << 21) | \
    (enpassant << 22) | \
    (castling << 23)    \

#define getMoveSource(move) (move & 0x3f)
#define getMoveTarget(move) ((move & 0xfc0) >> 6)
#define getMovePiece(move) ((move & 0xf000) >> 12)
#define getMovePromoted(move) ((move & 0xf0000) >> 16)
#define getMoveCapture(move) (move & 0x100000)
#define getMoveDouble(move) (move & 0x200000)
#define getMoveEnpassant(move) (move & 0x400000)
#define getMoveCastling(move) (move & 0x800000)

#define copyBoard()                                                      \
    uint64_t boardCopy[12], occupancyCopy[3];                            \
    int sideCopy, enpassantCopy, castleCopy;                             \
    memcpy(boardCopy, board, 96);                                		 \
    memcpy(occupancyCopy, occupancy, 24);                            	 \
    sideCopy = side, enpassantCopy = enpassant, castleCopy = castling;   \
    uint64_t hashKeyCopy = hashKey;                                      \
	int fiftyMoveCopy = fiftyMove; 

#define takeBack()                                                       \
    memcpy(board, boardCopy, 96);                                		 \
    memcpy(occupancy, occupancyCopy, 24);                                \
    side = sideCopy, enpassant = enpassantCopy, castling = castleCopy;   \
    hashKey = hashKeyCopy;												 \
	fiftyMove = fiftyMoveCopy;

#define INF 50000
#define mateValue 49000
#define mateScore 48000

#define HASH_SIZE 0x300000
#define HFLAG_EXACT 0
#define HFLAG_ALPHA 1
#define HFLAG_BETA 2
#define NO_HASH_ENTRY -1

enum Square {
    a8, b8, c8, d8, e8, f8, g8, h8,
    a7, b7, c7, d7, e7, f7, g7, h7,
    a6, b6, c6, d6, e6, f6, g6, h6,
    a5, b5, c5, d5, e5, f5, g5, h5,
    a4, b4, c4, d4, e4, f4, g4, h4,
    a3, b3, c3, d3, e3, f3, g3, h3,
    a2, b2, c2, d2, e2, f2, g2, h2,
    a1, b1, c1, d1, e1, f1, g1, h1, noSqr
};

enum Side { WHITE, BLACK, BOTH };
enum CastlingRights { WK = 1, WQ = 2, BK = 4, BQ = 8 };
enum { ALL_MOVES, ONLY_CAPTURES };
enum { ROOK, BISHOP };
enum Piece { P, N, B, R, Q, K, p, n, b, r, q, k };

typedef struct {
	int moves[256];
	int count;
} MoveList;

typedef struct {
	uint64_t hashKey;
	int depth;
	int score;
	int flag;
} TransposTable;

map<char, int> charToPiece = {
    {'P', P},
    {'N', N},
    {'B', B},
    {'R', R},
    {'Q', Q},
    {'K', K},
    {'p', p},
    {'n', n},
    {'b', b},
    {'r', r},
    {'q', q},
    {'k', k},
};

map<int, char> pieceToChar = {
    {P, 'P'},
    {N, 'N'},
    {B, 'B'},
    {R, 'R'},
    {Q, 'Q'},
    {K, 'K'},
    {p, 'p'},
    {n, 'n'},
    {b, 'b'},
    {r, 'r'},
    {q, 'q'},
    {k, 'k'},
};

const char* squareToCoords[] = {
	"a8", "b8", "c8", "d8", "e8", "f8", "g8", "h8",
	"a7", "b7", "c7", "d7", "e7", "f7", "g7", "h7",
	"a6", "b6", "c6", "d6", "e6", "f6", "g6", "h6",
	"a5", "b5", "c5", "d5", "e5", "f5", "g5", "h5",
	"a4", "b4", "c4", "d4", "e4", "f4", "g4", "h4",
	"a3", "b3", "c3", "d3", "e3", "f3", "g3", "h3",
	"a2", "b2", "c2", "d2", "e2", "f2", "g2", "h2",
	"a1", "b1", "c1", "d1", "e1", "f1", "g1", "h1"
};

char asciiPieces[13] = "PNBRQKpnbrqk";

const int bishopRelevantBits[64] = {
	6, 5, 5, 5, 5, 5, 5, 6,
	5, 5, 5, 5, 5, 5, 5, 5,
	5, 5, 7, 7, 7, 7, 5, 5,
	5, 5, 7, 9, 9, 7, 5, 5,
	5, 5, 7, 9, 9, 7, 5, 5,
	5, 5, 7, 7, 7, 7, 5, 5,
	5, 5, 5, 5, 5, 5, 5, 5,
	6, 5, 5, 5, 5, 5, 5, 6
};

const int rookRelevantBits[64] = {
	12, 11, 11, 11, 11, 11, 11, 12,
	11, 10, 10, 10, 10, 10, 10, 11,
	11, 10, 10, 10, 10, 10, 10, 11,
	11, 10, 10, 10, 10, 10, 10, 11,
	11, 10, 10, 10, 10, 10, 10, 11,
	11, 10, 10, 10, 10, 10, 10, 11,
	11, 10, 10, 10, 10, 10, 10, 11,
	12, 11, 11, 11, 11, 11, 11, 12
};

uint64_t rookMagicNumbers[64] = {
	0x8a80104000800020ULL,
	0x140002000100040ULL,
	0x2801880a0017001ULL,
	0x100081001000420ULL,
	0x200020010080420ULL,
	0x3001c0002010008ULL,
	0x8480008002000100ULL,
	0x2080088004402900ULL,
	0x800098204000ULL,
	0x2024401000200040ULL,
	0x100802000801000ULL,
	0x120800800801000ULL,
	0x208808088000400ULL,
	0x2802200800400ULL,
	0x2200800100020080ULL,
	0x801000060821100ULL,
	0x80044006422000ULL,
	0x100808020004000ULL,
	0x12108a0010204200ULL,
	0x140848010000802ULL,
	0x481828014002800ULL,
	0x8094004002004100ULL,
	0x4010040010010802ULL,
	0x20008806104ULL,
	0x100400080208000ULL,
	0x2040002120081000ULL,
	0x21200680100081ULL,
	0x20100080080080ULL,
	0x2000a00200410ULL,
	0x20080800400ULL,
	0x80088400100102ULL,
	0x80004600042881ULL,
	0x4040008040800020ULL,
	0x440003000200801ULL,
	0x4200011004500ULL,
	0x188020010100100ULL,
	0x14800401802800ULL,
	0x2080040080800200ULL,
	0x124080204001001ULL,
	0x200046502000484ULL,
	0x480400080088020ULL,
	0x1000422010034000ULL,
	0x30200100110040ULL,
	0x100021010009ULL,
	0x2002080100110004ULL,
	0x202008004008002ULL,
	0x20020004010100ULL,
	0x2048440040820001ULL,
	0x101002200408200ULL,
	0x40802000401080ULL,
	0x4008142004410100ULL,
	0x2060820c0120200ULL,
	0x1001004080100ULL,
	0x20c020080040080ULL,
	0x2935610830022400ULL,
	0x44440041009200ULL,
	0x280001040802101ULL,
	0x2100190040002085ULL,
	0x80c0084100102001ULL,
	0x4024081001000421ULL,
	0x20030a0244872ULL,
	0x12001008414402ULL,
	0x2006104900a0804ULL,
	0x1004081002402ULL
};

uint64_t bishopMagicNumbers[64] = {
	0x40040844404084ULL,
	0x2004208a004208ULL,
	0x10190041080202ULL,
	0x108060845042010ULL,
	0x581104180800210ULL,
	0x2112080446200010ULL,
	0x1080820820060210ULL,
	0x3c0808410220200ULL,
	0x4050404440404ULL,
	0x21001420088ULL,
	0x24d0080801082102ULL,
	0x1020a0a020400ULL,
	0x40308200402ULL,
	0x4011002100800ULL,
	0x401484104104005ULL,
	0x801010402020200ULL,
	0x400210c3880100ULL,
	0x404022024108200ULL,
	0x810018200204102ULL,
	0x4002801a02003ULL,
	0x85040820080400ULL,
	0x810102c808880400ULL,
	0xe900410884800ULL,
	0x8002020480840102ULL,
	0x220200865090201ULL,
	0x2010100a02021202ULL,
	0x152048408022401ULL,
	0x20080002081110ULL,
	0x4001001021004000ULL,
	0x800040400a011002ULL,
	0xe4004081011002ULL,
	0x1c004001012080ULL,
	0x8004200962a00220ULL,
	0x8422100208500202ULL,
	0x2000402200300c08ULL,
	0x8646020080080080ULL,
	0x80020a0200100808ULL,
	0x2010004880111000ULL,
	0x623000a080011400ULL,
	0x42008c0340209202ULL,
	0x209188240001000ULL,
	0x400408a884001800ULL,
	0x110400a6080400ULL,
	0x1840060a44020800ULL,
	0x90080104000041ULL,
	0x201011000808101ULL,
	0x1a2208080504f080ULL,
	0x8012020600211212ULL,
	0x500861011240000ULL,
	0x180806108200800ULL,
	0x4000020e01040044ULL,
	0x300000261044000aULL,
	0x802241102020002ULL,
	0x20906061210001ULL,
	0x5a84841004010310ULL,
	0x4010801011c04ULL,
	0xa010109502200ULL,
	0x4a02012000ULL,
	0x500201010098b028ULL,
	0x8040002811040900ULL,
	0x28000010020204ULL,
	0x6000020202d0240ULL,
	0x8918844842082200ULL,
	0x4010011029020020ULL
};

// castling rights update constants
const int castlingRights[64] = {
     7, 15, 15, 15,  3, 15, 15, 11,
    15, 15, 15, 15, 15, 15, 15, 15,
    15, 15, 15, 15, 15, 15, 15, 15,
    15, 15, 15, 15, 15, 15, 15, 15,
    15, 15, 15, 15, 15, 15, 15, 15,
    15, 15, 15, 15, 15, 15, 15, 15,
    15, 15, 15, 15, 15, 15, 15, 15,
    13, 15, 15, 15, 12, 15, 15, 14
};

const uint64_t NOT_A_FILE = 18374403900871474942ULL;
const uint64_t NOT_H_FILE = 9187201950435737471ULL;
const uint64_t NOT_GH_FILE = 4557430888798830399ULL;
const uint64_t NOT_AB_FILE = 18229723555195321596ULL;

uint64_t pawnAttacks[2][64];
uint64_t knightAttacks[64];
uint64_t kingAttacks[64];
uint64_t bishopMasks[64];
uint64_t rookMasks[64];
uint64_t queenAttacks[64];
uint64_t rookAttacks[64][4096];
uint64_t bishopAttacks[64][512];

uint64_t hashKey = 0;

int ply = 0;
long nodes = 0;

int pvTable[64][64];
int pvLength[64];

int killerMoves[2][64];
int historyMoves[12][64];

uint64_t repTable[1000];
int repIndex = 0;

TransposTable tt[HASH_SIZE];

uint64_t pieceKeys[12][64];
uint64_t castlingKeys[16];
uint64_t enpassantKeys[64];
uint64_t sideKey = 0;

uint64_t board[12];
uint64_t occupancy[3];

int side = WHITE;
int enpassant = noSqr;
int castling = 0;
int fiftyMove = 0;

// MVV LVA [attacker][victim]
static int MVV_LVA[12][12] = {
 	105, 205, 305, 405, 505, 605,  105, 205, 305, 405, 505, 605,
	104, 204, 304, 404, 504, 604,  104, 204, 304, 404, 504, 604,
	103, 203, 303, 403, 503, 603,  103, 203, 303, 403, 503, 603,
	102, 202, 302, 402, 502, 602,  102, 202, 302, 402, 502, 602,
	101, 201, 301, 401, 501, 601,  101, 201, 301, 401, 501, 601,
	100, 200, 300, 400, 500, 600,  100, 200, 300, 400, 500, 600,

	105, 205, 305, 405, 505, 605,  105, 205, 305, 405, 505, 605,
	104, 204, 304, 404, 504, 604,  104, 204, 304, 404, 504, 604,
	103, 203, 303, 403, 503, 603,  103, 203, 303, 403, 503, 603,
	102, 202, 302, 402, 502, 602,  102, 202, 302, 402, 502, 602,
	101, 201, 301, 401, 501, 601,  101, 201, 301, 401, 501, 601,
	100, 200, 300, 400, 500, 600,  100, 200, 300, 400, 500, 600
};

// UCI variables
bool quit = 0;
int movestogo = 30;
int movetime = -1;
int tTime = -1;
int inc = 0;
int starttime = 0;
int stoptime = 0;
int timeset = 0;
bool stopped = 0;

int getTimeMS()
{
	struct timeval time_value;
    gettimeofday(&time_value, NULL);
    return time_value.tv_sec * 1000 + time_value.tv_usec / 1000;
}

static inline int countBits(uint64_t bb)
{
	int count = 0;

	while (bb)
	{
		bb &= bb - 1;
		count++;
	}

	return count;
}

// gets the least significant first bit index
static inline int getLSB(uint64_t bb)
{
	int count = 0;

	while ((bb & 1) == 0)
	{
		count++;
		bb >>= 1;
	}

	return count;
}

uint64_t setOccupancy(int index, int bitsInMask, uint64_t attackMask)
{
	uint64_t occupancy = 0ULL;

	for (int count = 0; count < bitsInMask; count++)
	{
		int square = getLSB(attackMask);

		zeroBit(attackMask, square);

		if (index & (1 << count))
			occupancy |= (1ULL << square);
	}

	return occupancy;
}

uint64_t maskPawnAttacks(int side, int square)
{
	uint64_t attacks = 0ULL;
	uint64_t bitboard = 0ULL;
	
	setBit(bitboard, square);
	
	if (side == WHITE)
	{
		attacks |= (bitboard >> 7) & NOT_A_FILE;
		attacks |= (bitboard >> 9) & NOT_H_FILE;
	}
	else
	{
		attacks |= (bitboard << 7) & NOT_H_FILE;
		attacks |= (bitboard << 9) & NOT_A_FILE;
	}
	
	return attacks;
}
uint64_t maskKnightAttacks(int sqr)
{
	uint64_t bitboard = 0ULL;
	uint64_t attacks = 0ULL;

	setBit(bitboard, sqr);

	attacks |= (bitboard >> 15) & NOT_A_FILE;
	attacks |= (bitboard >> 17) & NOT_H_FILE;
	attacks |= (bitboard >> 10) & NOT_GH_FILE;
	attacks |= (bitboard >> 6) & NOT_AB_FILE;
	attacks |= (bitboard << 15) & NOT_H_FILE;
	attacks |= (bitboard << 17) & NOT_A_FILE;
	attacks |= (bitboard << 10) & NOT_AB_FILE;
	attacks |= (bitboard << 6) & NOT_GH_FILE;

	return attacks;
}

uint64_t maskKingAttacks(int sqr)
{
	uint64_t bitboard = 0ULL;
	uint64_t attacks = 0ULL;

	setBit(bitboard, sqr);

	attacks |= (bitboard >> 7) & NOT_A_FILE;
	attacks |= bitboard >> 8;
	attacks |= (bitboard >> 9) & NOT_H_FILE;
	attacks |= (bitboard >> 1) & NOT_H_FILE;
	attacks |= (bitboard << 7) & NOT_H_FILE;
	attacks |= bitboard << 8;
	attacks |= (bitboard << 9) & NOT_A_FILE;
	attacks |= (bitboard << 1) & NOT_A_FILE;

	return attacks;
}

uint64_t maskBishopAttacks(int sqr)
{
	uint64_t attacks = 0ULL;

	int r, f;

	int tr = sqr / 8;
	int tf = sqr % 8;

	for (r = tr + 1, f = tf + 1; r <= 6 && f <= 6; r++, f++) attacks |= (1ULL << (r * 8 + f));
	for (r = tr - 1, f = tf + 1; r >= 1 && f <= 6; r--, f++) attacks |= (1ULL << (r * 8 + f));
	for (r = tr + 1, f = tf - 1; r <= 6 && f >= 1; r++, f--) attacks |= (1ULL << (r * 8 + f));
	for (r = tr - 1, f = tf - 1; r >= 1 && f >= 1; r--, f--) attacks |= (1ULL << (r * 8 + f));

	return attacks;
}

uint64_t maskRookAttacks(int sqr)
{
	uint64_t attacks = 0ULL;

	int r, f;

	int tr = sqr / 8;
	int tf = sqr % 8;

	for (r = tr + 1; r <= 6; r++) attacks |= (1ULL << (r * 8 + tf));
	for (r = tr - 1; r >= 1; r--) attacks |= (1ULL << (r * 8 + tf));
	for (f = tf + 1; f <= 6; f++) attacks |= (1ULL << (tr * 8 + f));
	for (f = tf - 1; f >= 1; f--) attacks |= (1ULL << (tr * 8 + f));

	return attacks;
}

uint64_t bishopAttacksOTF(int sqr, uint64_t blockers)
{
	uint64_t attacks = 0ULL;

	int r, f;

	int tr = sqr / 8;
	int tf = sqr % 8;

	for (r = tr + 1, f = tf + 1; r <= 7 && f <= 7; r++, f++)
	{
		attacks |= (1ULL << (r * 8 + f));
		if ((1ULL << (r * 8 + f)) & blockers) break;
	}
	for (r = tr - 1, f = tf + 1; r >= 0 && f <= 7; r--, f++)
	{
		attacks |= (1ULL << (r * 8 + f));
		if ((1ULL << (r * 8 + f)) & blockers) break;
	}
	for (r = tr + 1, f = tf - 1; r <= 7 && f >= 0; r++, f--)
	{
		attacks |= (1ULL << (r * 8 + f));
		if ((1ULL << (r * 8 + f)) & blockers) break;
	}
	for (r = tr - 1, f = tf - 1; r >= 0 && f >= 0; r--, f--)
	{
		attacks |= (1ULL << (r * 8 + f));
		if ((1ULL << (r * 8 + f)) & blockers) break;
	}

	return attacks;
}

uint64_t rookAttacksOTF(int square, uint64_t blockers)
{
	uint64_t attacks = 0ULL;

	int r, f;

	int tr = square / 8;
	int tf = square % 8;

	for (r = tr + 1; r <= 7; r++)
	{
		attacks |= (1ULL << (r * 8 + tf));
		if ((1ULL << (r * 8 + tf)) & blockers) break;
	}

	for (r = tr - 1; r >= 0; r--)
	{
		attacks |= (1ULL << (r * 8 + tf));
		if ((1ULL << (r * 8 + tf)) & blockers) break;
	}

	for (f = tf + 1; f <= 7; f++)
	{
		attacks |= (1ULL << (tr * 8 + f));
		if ((1ULL << (tr * 8 + f)) & blockers) break;
	}

	for (f = tf - 1; f >= 0; f--)
	{
		attacks |= (1ULL << (tr * 8 + f));
		if ((1ULL << (tr * 8 + f)) & blockers) break;
	}

	return attacks;
}

void printBitboard(uint64_t bb)
{
	for (int i = 0; i < 64; i++)
	{
		if (i % 8 == 0)
			cout << endl;

		cout << (int)getBit(bb, i);
	}

	cout << endl << endl;
}

void printBoard()
{
	for (int i = 0; i < 64; i++)
	{
		if (i % 8 == 0)
		{
			cout << endl;
			cout << 8 - (i / 8);
		}
		
		if (getBit(board[P], i)) cout << " P";
		else if (getBit(board[p], i)) cout << " p";
		else if (getBit(board[N], i)) cout << " N";
		else if (getBit(board[n], i)) cout << " n";
		else if (getBit(board[B], i)) cout << " B";
		else if (getBit(board[b], i)) cout << " b";
		else if (getBit(board[R], i)) cout << " R";
		else if (getBit(board[r], i)) cout << " r";
		else if (getBit(board[Q], i)) cout << " Q";
		else if (getBit(board[q], i)) cout << " q";
		else if (getBit(board[K], i)) cout << " K";
		else if (getBit(board[k], i)) cout << " k";
		else cout << " .";
	}

	cout << endl << "  a b c d e f g h" << endl;

	cout << endl << "Side: " << (side == WHITE ? "white" : "black") << endl;
	cout << "Enpassant: " << ((enpassant != noSqr) ? squareToCoords[enpassant] : "no") << endl;
	cout << "Castling: " << ((castling & WK) ? 'K' : '-') << ((castling & WQ) ? 'Q' : '-')
		 << ((castling & BK) ? 'k' : '-') << ((castling & BQ) ? 'q' : '-') << endl;
	cout << "Bitboard: " << (uint64_t)occupancy[BOTH] << "ULL" << endl << endl;
}

uint64_t generateHashKey()
{
	uint64_t finalKey = 0;
	uint64_t bb = 0;
	
	for (int piece = P; piece <= k; piece++)
	{
		bb = board[piece];
		
		while (bb)
		{
			int square = getLSB(bb);
			finalKey ^= pieceKeys[piece][square];
			zeroBit(bb, square);
		}
	}
	
	if (enpassant != noSqr)
		finalKey ^= enpassantKeys[enpassant];
		
	finalKey ^= castlingKeys[castling];
	
	if (side == BLACK)
		finalKey ^= sideKey;
		
	return finalKey;
}


void parseFen(char* fen)
{
	side = 0;
	enpassant = noSqr;
	castling = 0;
	ply = 0;
	repIndex = 0;
	fiftyMove = 0;

	memset(board, 0, sizeof(board));
	memset(occupancy, 0, sizeof(occupancy));
	memset(repTable, 0, sizeof(repTable));

	for (int rank = 0; rank < 8; rank++)
	{
		for (int file = 0; file < 8; file++)
		{
			int square = rank * 8 + file;

			if ((*fen >= 'a' && *fen <= 'z') || (*fen >= 'A' && *fen <= 'Z'))
			{
				int piece = charToPiece[*fen];
				setBit(board[piece], square);
				fen++;
			}

			if (*fen >= '0' && *fen <= '9')
			{
				int offset = *fen - '0';
				int target_piece = -1;

				for (int piece = P; piece <= k; piece++)
				{
					if (getBit(board[piece], square))
						target_piece = piece;
				}

				if (target_piece == -1)
					file--;

				file += offset;

				fen++;
			}

			if (*fen == '/')
				*fen++;
		}
	}

	// go to side to move
	fen++;

	(*fen == 'w') ? (side = WHITE) : (side = BLACK);

	// go to castling rights
	fen += 2;

	while (*fen != ' ')
	{
		switch (*fen)
		{
		case 'K': castling |= WK; break;
		case 'Q': castling |= WQ; break;
		case 'k': castling |= BK; break;
		case 'q': castling |= BQ; break;
		case '-': break;
		}

		fen++;
	}

	// go to enpassant square
	fen++;

	if (*fen != '-')
	{
		int file = fen[0] - 'a';
		int rank = 8 - (fen[1] - '0');

		enpassant = rank * 8 + file;
	}
	else
		enpassant = noSqr;

	for (int piece = P; piece <= K; piece++)
		occupancy[WHITE] |= board[piece];

	for (int piece = p; piece <= k; piece++)
		occupancy[BLACK] |= board[piece];

    occupancy[BOTH] = occupancy[WHITE] | occupancy[BLACK];

	hashKey = generateHashKey();
}

void initAttackMasks()
{
	for (int square = 0; square < 64; square++)
	{
		pawnAttacks[WHITE][square] = maskPawnAttacks(WHITE, square);
		pawnAttacks[BLACK][square] = maskPawnAttacks(BLACK, square);
		knightAttacks[square] = maskKnightAttacks(square);
		kingAttacks[square] = maskKingAttacks(square);
		bishopMasks[square] = maskBishopAttacks(square);
		rookMasks[square] = maskRookAttacks(square);
	}
}

void initSliderAttacks(bool isBishop)
{
	for (int sqr = 0; sqr < 64; sqr++)
	{
		uint64_t attackMask = isBishop ? bishopMasks[sqr] : rookMasks[sqr];

		int relevantBitsCount = countBits(attackMask);

		int occupancyIndices = (1 << relevantBitsCount);

		for (int index = 0; index < occupancyIndices; index++)
		{
			if (isBishop)
			{
				uint64_t occupancy = setOccupancy(index, relevantBitsCount, attackMask);
				int magic_index = (occupancy * bishopMagicNumbers[sqr]) >> (64 - bishopRelevantBits[sqr]);
				bishopAttacks[sqr][magic_index] = bishopAttacksOTF(sqr, occupancy);
			}
			else
			{
				uint64_t occupancy = setOccupancy(index, relevantBitsCount, attackMask);
				int magic_index = (occupancy * rookMagicNumbers[sqr]) >> (64 - rookRelevantBits[sqr]);
				rookAttacks[sqr][magic_index] = rookAttacksOTF(sqr, occupancy);
			}
		}
	}
}

static inline uint64_t getRookAttacks(int sqr, uint64_t occupancy)
{
	occupancy &= rookMasks[sqr];
	occupancy *= rookMagicNumbers[sqr];
	occupancy >>= 64 - rookRelevantBits[sqr];

	return rookAttacks[sqr][occupancy];
}

static inline uint64_t getBishopAttacks(int sqr, uint64_t occupancy)
{
	occupancy &= bishopMasks[sqr];
	occupancy *= bishopMagicNumbers[sqr];
	occupancy >>= 64 - bishopRelevantBits[sqr];

	return bishopAttacks[sqr][occupancy];
}

static inline uint64_t getQueenAttacks(int sqr, uint64_t occupancy) 
{ 
	return getBishopAttacks(sqr, occupancy) | getRookAttacks(sqr, occupancy); 
}

static inline void addMove(MoveList* moves, int move)
{
	moves->moves[moves->count++] = move;
}

static inline bool isSquareAttacked(int square, int side)
{
	if (side == WHITE && (pawnAttacks[BLACK][square] & board[P])) return true;
	if (side == BLACK && (pawnAttacks[WHITE][square] & board[p])) return true;
	if (knightAttacks[square] & (side == WHITE ? board[N] : board[n])) return true;
	if (kingAttacks[square] & (side == WHITE ? board[K] : board[k])) return true;
	if (getBishopAttacks(square, occupancy[BOTH]) & (side == WHITE ? board[B] : board[b])) return true;
	if (getRookAttacks(square, occupancy[BOTH]) & (side == WHITE ? board[R] : board[r])) return true;
	if (getQueenAttacks(square, occupancy[BOTH]) & ((side == WHITE ? board[Q] : board[q]))) return true;

	return false;
}

static inline void generateMoves(MoveList* moves)
{
	int fromSquare, toSquare;

	uint64_t bitboard, attacks;

	moves->count = 0;

	for (int piece = P; piece <= k; piece++)
	{
		bitboard = board[piece];

		if (side == WHITE)
		{
			if (piece == P)
			{
				while (bitboard)
				{
					fromSquare = getLSB(bitboard);
					toSquare = fromSquare - 8;

					// generate quiet pawn moves
					if (!getBit(occupancy[BOTH], toSquare))
					{
						// promotion
						if (fromSquare >= a7 && fromSquare <= h7)
						{
							addMove(moves, encodeMove(fromSquare, toSquare, piece, Q, 0, 0, 0, 0));
							addMove(moves, encodeMove(fromSquare, toSquare, piece, R, 0, 0, 0, 0));
							addMove(moves, encodeMove(fromSquare, toSquare, piece, B, 0, 0, 0, 0));
							addMove(moves, encodeMove(fromSquare, toSquare, piece, N, 0, 0, 0, 0));
						}
						else
						{
							// single pawn push
							addMove(moves, encodeMove(fromSquare, toSquare, piece, 0, 0, 0, 0, 0));

							// double pawn push
							if ((fromSquare >= a2 && fromSquare <= h2) && !getBit(occupancy[BOTH], toSquare - 8))
								addMove(moves, encodeMove(fromSquare, toSquare - 8, piece, 0, 0, 1, 0, 0));
						}
					}

					attacks = pawnAttacks[side][fromSquare] & occupancy[BLACK];

					// generate pawn captures
					while (attacks)
					{
						toSquare = getLSB(attacks);

						if (fromSquare >= a7 && fromSquare <= h7)
						{
							addMove(moves, encodeMove(fromSquare, toSquare, piece, Q, 1, 0, 0, 0));
							addMove(moves, encodeMove(fromSquare, toSquare, piece, R, 1, 0, 0, 0));
							addMove(moves, encodeMove(fromSquare, toSquare, piece, B, 1, 0, 0, 0));
							addMove(moves, encodeMove(fromSquare, toSquare, piece, N, 1, 0, 0, 0));
						}
						else
							addMove(moves, encodeMove(fromSquare, toSquare, piece, 0, 1, 0, 0, 0));

						zeroBit(attacks, toSquare);
					}

					// generate enpassant captures
					if (enpassant != noSqr)
					{
						uint64_t enpassant_attacks = pawnAttacks[side][fromSquare] & (1ULL << enpassant);

						if (enpassant_attacks)
						{
							int target_enpassant = getLSB(enpassant_attacks);
							addMove(moves, encodeMove(fromSquare, target_enpassant, piece, 0, 1, 0, 1, 0));
						}
					}

					zeroBit(bitboard, fromSquare);
				}
			}
			else if (piece == K)
			{
				if (castling & WK)
				{
					if (!getBit(occupancy[BOTH], f1) && !getBit(occupancy[BOTH], g1))
					{
						if (!isSquareAttacked(e1, BLACK) && !isSquareAttacked(f1, BLACK))
							addMove(moves, encodeMove(e1, g1, piece, 0, 0, 0, 0, 1));
					}
				}
				else if (castling & WQ)
				{
					if (!getBit(occupancy[BOTH], d1) && !getBit(occupancy[BOTH], c1) && !getBit(occupancy[BOTH], b1))
					{
						if (!isSquareAttacked(e1, BLACK) && !isSquareAttacked(d1, BLACK))
							addMove(moves, encodeMove(e1, c1, piece, 0, 0, 0, 0, 1));
					}
				}
			}
		}
		else
		{
			if (piece == p)
			{
				while (bitboard)
				{
					fromSquare = getLSB(bitboard);
					toSquare = fromSquare + 8;


					// generate quiet pawn moves
					if (!getBit(occupancy[BOTH], toSquare))
					{
						if (fromSquare >= a2 && fromSquare <= h2)
						{
							addMove(moves, encodeMove(fromSquare, toSquare, piece, q, 0, 0, 0, 0));
							addMove(moves, encodeMove(fromSquare, toSquare, piece, r, 0, 0, 0, 0));
							addMove(moves, encodeMove(fromSquare, toSquare, piece, b, 0, 0, 0, 0));
							addMove(moves, encodeMove(fromSquare, toSquare, piece, n, 0, 0, 0, 0));
						}
						else
						{
							// generate single pawn pushes
							addMove(moves, encodeMove(fromSquare, toSquare, piece, 0, 0, 0, 0, 0));

							// generate double pawn pushes
							if ((fromSquare >= a7 && fromSquare <= h7) && !getBit(occupancy[BOTH], toSquare + 8))
								addMove(moves, encodeMove(fromSquare, toSquare + 8, piece, 0, 0, 1, 0, 0));
						}
					}

					attacks = pawnAttacks[side][fromSquare] & occupancy[WHITE];

					// generate pawn captures
					while (attacks)
					{
						toSquare = getLSB(attacks);

						if (fromSquare >= a2 && fromSquare <= h2)
						{
							addMove(moves, encodeMove(fromSquare, toSquare, piece, q, 1, 0, 0, 0));
							addMove(moves, encodeMove(fromSquare, toSquare, piece, r, 1, 0, 0, 0));
							addMove(moves, encodeMove(fromSquare, toSquare, piece, b, 1, 0, 0, 0));
							addMove(moves, encodeMove(fromSquare, toSquare, piece, n, 1, 0, 0, 0));
						}
						else
							addMove(moves, encodeMove(fromSquare, toSquare, piece, 0, 1, 0, 0, 0));

						zeroBit(attacks, toSquare);
					}

					// generate enpassant captures
					if (enpassant != noSqr)
					{
						uint64_t enpassant_attacks = pawnAttacks[side][fromSquare] & (1ULL << enpassant);

						if (enpassant_attacks)
						{
							int target_enpassant = getLSB(enpassant_attacks);
							addMove(moves, encodeMove(fromSquare, target_enpassant, piece, 0, 1, 0, 1, 0));
						}
					}

					zeroBit(bitboard, fromSquare);
				}
			}
			else if (piece == k)
			{
				if (castling & BK)
				{
					if (!getBit(occupancy[BOTH], f8) && !getBit(occupancy[BOTH], g8))
					{
						if (!isSquareAttacked(e8, WHITE) && !isSquareAttacked(f8, WHITE))
							addMove(moves, encodeMove(e8, g8, piece, 0, 0, 0, 0, 1));
					}
				}
				else if (castling & BQ)
				{
					if (!getBit(occupancy[BOTH], d8) && !getBit(occupancy[BOTH], c8) && !getBit(occupancy[BOTH], b8))
					{
						if (!isSquareAttacked(e8, WHITE) && !isSquareAttacked(d8, WHITE))
						{
							addMove(moves, encodeMove(e8, c8, piece, 0, 0, 0, 0, 1));
						}
					}
				}
			}
		}

		// generate knight moves
		if ((side == WHITE) ? piece == N : piece == n)
		{
			while (bitboard)
			{
				fromSquare = getLSB(bitboard);

				attacks = knightAttacks[fromSquare] & ((side == WHITE) ? ~occupancy[WHITE] : ~occupancy[BLACK]);

				while (attacks)
				{
					toSquare = getLSB(attacks);

					// quiet moves
					if (!getBit(((side == WHITE) ? occupancy[BLACK] : occupancy[WHITE]), toSquare))
						addMove(moves, encodeMove(fromSquare, toSquare, piece, 0, 0, 0, 0, 0));
					// capture moves
					else
						addMove(moves, encodeMove(fromSquare, toSquare, piece, 0, 1, 0, 0, 0));

					zeroBit(attacks, toSquare);
				}

				zeroBit(bitboard, fromSquare);
			}
		}

		// generate bishop moves
		if ((side == WHITE) ? piece == B : piece == b)
		{
			while (bitboard)
			{
				fromSquare = getLSB(bitboard);

				attacks = getBishopAttacks(fromSquare, occupancy[BOTH]) & ((side == WHITE) ? ~occupancy[WHITE] : ~occupancy[BLACK]);

				while (attacks)
				{
					toSquare = getLSB(attacks);

					// quiet moves
					if (!getBit(((side == WHITE) ? occupancy[BLACK] : occupancy[WHITE]), toSquare))
						addMove(moves, encodeMove(fromSquare, toSquare, piece, 0, 0, 0, 0, 0));
					// capture moves
					else
						addMove(moves, encodeMove(fromSquare, toSquare, piece, 0, 1, 0, 0, 0));

					zeroBit(attacks, toSquare);
				}

				zeroBit(bitboard, fromSquare);
			}
		}

		// generate rook moves
		if ((side == WHITE) ? piece == R : piece == r)
		{
			while (bitboard)
			{
				fromSquare = getLSB(bitboard);

				attacks = getRookAttacks(fromSquare, occupancy[BOTH]) & ((side == WHITE) ? ~occupancy[WHITE] : ~occupancy[BLACK]);

				while (attacks)
				{
					toSquare = getLSB(attacks);

					// quiet moves
					if (!getBit(((side == WHITE) ? occupancy[BLACK] : occupancy[WHITE]), toSquare))
						addMove(moves, encodeMove(fromSquare, toSquare, piece, 0, 0, 0, 0, 0));
					// capture moves
					else
						addMove(moves, encodeMove(fromSquare, toSquare, piece, 0, 1, 0, 0, 0));

					zeroBit(attacks, toSquare);
				}

				zeroBit(bitboard, fromSquare);
			}
		}

		// generate queen moves
		if ((side == WHITE) ? piece == Q : piece == q)
		{
			while (bitboard)
			{
				fromSquare = getLSB(bitboard);

				attacks = getQueenAttacks(fromSquare, occupancy[BOTH]) & ((side == WHITE) ? ~occupancy[WHITE] : ~occupancy[BLACK]);

				while (attacks)
				{
					toSquare = getLSB(attacks);

					// quiet moves
					if (!getBit(((side == WHITE) ? occupancy[BLACK] : occupancy[WHITE]), toSquare))
						addMove(moves, encodeMove(fromSquare, toSquare, piece, 0, 0, 0, 0, 0));
					// capture moves
					else
						addMove(moves, encodeMove(fromSquare, toSquare, piece, 0, 1, 0, 0, 0));

					zeroBit(attacks, toSquare);
				}

				zeroBit(bitboard, fromSquare);
			}
		}

		// generate king moves
		if ((side == WHITE) ? piece == K : piece == k)
		{
			while (bitboard)
			{
				fromSquare = getLSB(bitboard);

				attacks = kingAttacks[fromSquare] & ((side == WHITE) ? ~occupancy[WHITE] : ~occupancy[BLACK]);

				while (attacks)
				{
					toSquare = getLSB(attacks);

					// quiet moves
					if (!getBit(((side == WHITE) ? occupancy[BLACK] : occupancy[WHITE]), toSquare))
						addMove(moves, encodeMove(fromSquare, toSquare, piece, 0, 0, 0, 0, 0));
					// capture moves
					else
						addMove(moves, encodeMove(fromSquare, toSquare, piece, 0, 1, 0, 0, 0));

					zeroBit(attacks, toSquare);
				}

				zeroBit(bitboard, fromSquare);
			}
		}
	}
}

static inline void generateCaptures(MoveList* moves)
{
	int fromSquare, toSquare;

	uint64_t bitboard, attacks;

	moves->count = 0;

	for (int piece = P; piece <= k; piece++)
	{
		bitboard = board[piece];

		if (side == WHITE)
		{
			if (piece == P)
			{
				while (bitboard)
				{
					fromSquare = getLSB(bitboard);

					attacks = pawnAttacks[side][fromSquare] & occupancy[BLACK];

					// generate pawn captures
					while (attacks)
					{
						toSquare = getLSB(attacks);

						if (fromSquare >= a7 && fromSquare <= h7)
						{
							addMove(moves, encodeMove(fromSquare, toSquare, piece, Q, 1, 0, 0, 0));
							addMove(moves, encodeMove(fromSquare, toSquare, piece, R, 1, 0, 0, 0));
							addMove(moves, encodeMove(fromSquare, toSquare, piece, B, 1, 0, 0, 0));
							addMove(moves, encodeMove(fromSquare, toSquare, piece, N, 1, 0, 0, 0));
						}
						else
							addMove(moves, encodeMove(fromSquare, toSquare, piece, 0, 1, 0, 0, 0));

						zeroBit(attacks, toSquare);
					}

					// generate enpassant captures
					if (enpassant != noSqr)
					{
						uint64_t enpassant_attacks = pawnAttacks[side][fromSquare] & (1ULL << enpassant);

						if (enpassant_attacks)
						{
							int target_enpassant = getLSB(enpassant_attacks);
							addMove(moves, encodeMove(fromSquare, target_enpassant, piece, 0, 1, 0, 1, 0));
						}
					}

					zeroBit(bitboard, fromSquare);
				}
			}
		}
		else
		{
			if (piece == p)
			{
				while (bitboard)
				{
					fromSquare = getLSB(bitboard);

					attacks = pawnAttacks[side][fromSquare] & occupancy[WHITE];

					// generate pawn captures
					while (attacks)
					{
						toSquare = getLSB(attacks);

						if (fromSquare >= a2 && fromSquare <= h2)
						{
							addMove(moves, encodeMove(fromSquare, toSquare, piece, q, 1, 0, 0, 0));
							addMove(moves, encodeMove(fromSquare, toSquare, piece, r, 1, 0, 0, 0));
							addMove(moves, encodeMove(fromSquare, toSquare, piece, b, 1, 0, 0, 0));
							addMove(moves, encodeMove(fromSquare, toSquare, piece, n, 1, 0, 0, 0));
						}
						else
							addMove(moves, encodeMove(fromSquare, toSquare, piece, 0, 1, 0, 0, 0));

						zeroBit(attacks, toSquare);
					}

					// generate enpassant captures
					if (enpassant != noSqr)
					{
						uint64_t enpassant_attacks = pawnAttacks[side][fromSquare] & (1ULL << enpassant);

						if (enpassant_attacks)
						{
							int target_enpassant = getLSB(enpassant_attacks);
							addMove(moves, encodeMove(fromSquare, target_enpassant, piece, 0, 1, 0, 1, 0));
						}
					}

					zeroBit(bitboard, fromSquare);
				}
			}
		}

		// generate knight moves
		if ((side == WHITE) ? piece == N : piece == n)
		{
			while (bitboard)
			{
				fromSquare = getLSB(bitboard);

				attacks = knightAttacks[fromSquare] & ((side == WHITE) ? ~occupancy[WHITE] : ~occupancy[BLACK]);

				while (attacks)
				{
					toSquare = getLSB(attacks);

					if (getBit(((side == WHITE) ? occupancy[BLACK] : occupancy[WHITE]), toSquare))
						addMove(moves, encodeMove(fromSquare, toSquare, piece, 0, 1, 0, 0, 0));

					zeroBit(attacks, toSquare);
				}

				zeroBit(bitboard, fromSquare);
			}
		}

		// generate bishop moves
		if ((side == WHITE) ? piece == B : piece == b)
		{
			while (bitboard)
			{
				fromSquare = getLSB(bitboard);

				attacks = getBishopAttacks(fromSquare, occupancy[BOTH]) & ((side == WHITE) ? ~occupancy[WHITE] : ~occupancy[BLACK]);

				while (attacks)
				{
					toSquare = getLSB(attacks);

					// quiet moves
					if (getBit(((side == WHITE) ? occupancy[BLACK] : occupancy[WHITE]), toSquare))
						addMove(moves, encodeMove(fromSquare, toSquare, piece, 0, 1, 0, 0, 0));

					zeroBit(attacks, toSquare);
				}

				zeroBit(bitboard, fromSquare);
			}
		}

		// generate rook moves
		if ((side == WHITE) ? piece == R : piece == r)
		{
			while (bitboard)
			{
				fromSquare = getLSB(bitboard);

				attacks = getRookAttacks(fromSquare, occupancy[BOTH]) & ((side == WHITE) ? ~occupancy[WHITE] : ~occupancy[BLACK]);

				while (attacks)
				{
					toSquare = getLSB(attacks);

					if (getBit(((side == WHITE) ? occupancy[BLACK] : occupancy[WHITE]), toSquare))
						addMove(moves, encodeMove(fromSquare, toSquare, piece, 0, 1, 0, 0, 0));

					zeroBit(attacks, toSquare);
				}

				zeroBit(bitboard, fromSquare);
			}
		}

		// generate queen moves
		if ((side == WHITE) ? piece == Q : piece == q)
		{
			while (bitboard)
			{
				fromSquare = getLSB(bitboard);

				attacks = getQueenAttacks(fromSquare, occupancy[BOTH]) & ((side == WHITE) ? ~occupancy[WHITE] : ~occupancy[BLACK]);

				while (attacks)
				{
					toSquare = getLSB(attacks);

					if (getBit(((side == WHITE) ? occupancy[BLACK] : occupancy[WHITE]), toSquare))
						addMove(moves, encodeMove(fromSquare, toSquare, piece, 0, 1, 0, 0, 0));

					zeroBit(attacks, toSquare);
				}

				zeroBit(bitboard, fromSquare);
			}
		}

		// generate king moves
		if ((side == WHITE) ? piece == K : piece == k)
		{
			while (bitboard)
			{
				fromSquare = getLSB(bitboard);

				attacks = kingAttacks[fromSquare] & ((side == WHITE) ? ~occupancy[WHITE] : ~occupancy[BLACK]);

				while (attacks)
				{
					toSquare = getLSB(attacks);

					if (getBit(((side == WHITE) ? occupancy[BLACK] : occupancy[WHITE]), toSquare))
						addMove(moves, encodeMove(fromSquare, toSquare, piece, 0, 1, 0, 0, 0));

					zeroBit(attacks, toSquare);
				}

				zeroBit(bitboard, fromSquare);
			}
		}
	}
}

static inline int makeMove(int move)
{
	int fromSquare = getMoveSource(move);
    int toSquare = getMoveTarget(move);
    int piece = getMovePiece(move);
    int promotedPiece = getMovePromoted(move);
    int capture = getMoveCapture(move);
    int doublePush = getMoveDouble(move);
    int enpass = getMoveEnpassant(move);
    int castle = getMoveCastling(move);

	copyBoard();

	zeroBit(board[piece], fromSquare);
	setBit(board[piece], toSquare);
	
	hashKey ^= pieceKeys[piece][fromSquare];
	hashKey ^= pieceKeys[piece][toSquare];

	fiftyMove++;

	if (piece == P || piece == p)
		fiftyMove = 0;

	if (capture)
	{
		int startPiece, endPiece;

		if (side == WHITE)
		{
			startPiece = p;
			endPiece = k;
		}
		else
		{
			startPiece = P;
			endPiece = K;
		}
			
		for (int bbPiece = startPiece; bbPiece <= endPiece; bbPiece++)
		{
			if (getBit(board[bbPiece], toSquare))
			{
				zeroBit(board[bbPiece], toSquare);
				hashKey ^= pieceKeys[bbPiece][toSquare];
				break;
			}
		}

		fiftyMove = 0;
	}

	if (promotedPiece)
	{
		(side == WHITE) ? zeroBit(board[P], toSquare) : zeroBit(board[p], toSquare);
		(side == WHITE) ? hashKey ^= pieceKeys[P][toSquare] : hashKey ^= pieceKeys[p][toSquare];
		setBit(board[promotedPiece], toSquare);
		hashKey ^= pieceKeys[promotedPiece][toSquare];
	}

	if (enpass)
	{
		side == WHITE ? zeroBit(board[p], toSquare + 8) : zeroBit(board[P], toSquare - 8);
		side == WHITE ? hashKey ^= pieceKeys[p][toSquare + 8] : hashKey ^= pieceKeys[P][toSquare - 8];
	}
	
	if (enpassant != noSqr)
		hashKey ^= enpassantKeys[enpassant];

	enpassant = noSqr;

	if (doublePush)
	{
		if (side == WHITE)
		{
			enpassant = toSquare + 8;
			hashKey ^= enpassantKeys[toSquare + 8];
		}
		else
		{
			enpassant = toSquare - 8;
			hashKey ^= enpassantKeys[toSquare - 8];
		}
	}

	if (castle)
    {
        switch (toSquare)
        {
            // white castles king side
            case g1:
                // move H rook
                zeroBit(board[R], h1);
                setBit(board[R], f1);
                hashKey ^= pieceKeys[R][h1];
                hashKey ^= pieceKeys[R][f1];
                break;
                
            // white castles queen side
            case c1:
                // move A rook
                zeroBit(board[R], a1);
                setBit(board[R], d1);
                hashKey ^= pieceKeys[R][a1];
                hashKey ^= pieceKeys[R][d1];
                break;
                
            // black castles king side
            case g8:
                // move H rook
                zeroBit(board[r], h8);
                setBit(board[r], f8);
               	hashKey ^= pieceKeys[r][h8];
                hashKey ^= pieceKeys[r][f8];
                break;
                
            // black castles queen side
            case c8:
                // move A rook
                zeroBit(board[r], a8);
                setBit(board[r], d8);
                hashKey ^= pieceKeys[r][a8];
                hashKey ^= pieceKeys[r][d8];
                break;
        }
    }

	//hashKey ^= castlingKeys[castling];

	castling &= castlingRights[fromSquare];
	castling &= castlingRights[toSquare];
	
	hashKey ^= castlingKeys[castling];

    memset(occupancy, 0, 24);

    for (int bb_piece = P; bb_piece <= K; bb_piece++)
        occupancy[WHITE] |= board[bb_piece];

    for (int bb_piece = p; bb_piece <= k; bb_piece++)
        occupancy[BLACK] |= board[bb_piece];

	occupancy[BOTH] = occupancy[WHITE] | occupancy[BLACK];

    side ^= 1;
    hashKey ^= sideKey;

	if (isSquareAttacked(side == WHITE ? getLSB(board[k]) : getLSB(board[K]), side))
	{
		takeBack();
		return 0;
	}
	else
		return 1;
}

// UCI functions

int parseMove(char *move_string)
{
    MoveList move_list[1];
    generateMoves(move_list);
    
    int source_square = (move_string[0] - 'a') + (8 - (move_string[1] - '0')) * 8;
    int target_square = (move_string[2] - 'a') + (8 - (move_string[3] - '0')) * 8;
    
    for (int move_count = 0; move_count < move_list->count; move_count++)
    {
        int move = move_list->moves[move_count];

        if (source_square == getMoveSource(move) && target_square == getMoveTarget(move))
        {
            int promoted_piece = getMovePromoted(move);

            if (promoted_piece)
            {
                if ((promoted_piece == Q || promoted_piece == q) && move_string[4] == 'q')
                    return move;
                else if ((promoted_piece == R || promoted_piece == r) && move_string[4] == 'r')
                    return move;
                else if ((promoted_piece == B || promoted_piece == b) && move_string[4] == 'b')
                    return move;
                else if ((promoted_piece == N || promoted_piece == n) && move_string[4] == 'n')
                    return move;

                continue;
            }

            return move;
        }
    }

    return 0;
}

void parsePosition(char *command)
{
    command += 9;

    char *current_char = command;

    if (strncmp(command, "startpos", 8) == 0)
        parseFen(startPosition);
    else
    {
        current_char = strstr(command, "fen");

        if (current_char == NULL)
            parseFen(startPosition);
        else
        {
            current_char += 4;
            parseFen(current_char);
        }
    }

    current_char = strstr(command, "moves");

    if (current_char != NULL)
    {
        current_char += 6;

        while(*current_char)
        {
            int move = parseMove(current_char);
            
            if (move == 0)
				continue;
            
			repTable[++repIndex] = hashKey;
            makeMove(move);
            
            while (*current_char && *current_char != ' ') current_char++;

            current_char++;
        }        
    }

    printBoard();
}

int input_waiting()
{
	#ifndef WIN32
        fd_set readfds;
        struct timeval tv;
        FD_ZERO (&readfds);
        FD_SET (fileno(stdin), &readfds);
        tv.tv_sec=0; tv.tv_usec=0;
        select(16, &readfds, 0, 0, &tv);

        return (FD_ISSET(fileno(stdin), &readfds));
    #else
        static int init = 0, pipe;
        static HANDLE inh;
        DWORD dw;

        if (!init)
        {
            init = 1;
            inh = GetStdHandle(STD_INPUT_HANDLE);
            pipe = !GetConsoleMode(inh, &dw);
            if (!pipe)
            {
                SetConsoleMode(inh, dw & ~(ENABLE_MOUSE_INPUT|ENABLE_WINDOW_INPUT));
                FlushConsoleInputBuffer(inh);
            }
        }
        
        if (pipe)
        {
           if (!PeekNamedPipe(inh, NULL, 0, NULL, &dw, NULL)) return 1;
           return dw;
        }
        
        else
        {
           GetNumberOfConsoleInputEvents(inh, &dw);
           return dw <= 1 ? 0 : dw;
        }
    #endif
}

// read GUI/user input
void read_input()
{
	int bytes;

	char input[256] = "", * endc;

	if (input_waiting())
	{
		stopped = 1;

		do
			bytes = read(fileno(stdin), input, 256);
		while (bytes < 0);

		endc = strchr(input, '\n');

		if (endc) *endc = 0;

		if (strlen(input) > 0)
		{
			if (!strncmp(input, "quit", 4))
				quit = 1;
			else if (!strncmp(input, "stop", 4))
				quit = 1;
		}
	}
}

void communicate() {
	if (timeset == 1 && getTimeMS() > stoptime)
		stopped = 1;

	read_input();
}

static inline uint64_t rand64()
{
	return rand() ^ ((uint64_t)rand() << 15) ^ ((uint64_t)rand() << 30) ^ ((uint64_t)rand() << 45) ^ ((uint64_t)rand() << 60);
}

void initHashKeys()
{
	for (int piece = P; piece <= k; piece++)
		for (int square = 0; square < 64; square++)
			pieceKeys[piece][square] = rand64();
	
	for (int i = 0; i < 16; i++)
		castlingKeys[i] = rand64();
		
	for (int square = 0; square < 64; square++)
		enpassantKeys[square] = rand64();
		
	sideKey = rand64();
}

void clearHashTable()
{
	for (int i = 0; i < HASH_SIZE; i++)
	{
		tt[i].hashKey = 0ULL;
		tt[i].depth = 0;
		tt[i].score = 0;
		tt[i].flag = -1;
	}
}

static inline int probeHash(int depth, int alpha, int beta)
{
	TransposTable* hashEntry = &tt[hashKey % HASH_SIZE];
	
	if (hashEntry->hashKey == hashKey)
	{
		if (hashEntry->depth >= depth)
		{
			int score = hashEntry->score;

			if (score < -mateScore) score += ply;
            if (score > mateScore) score -= ply;

			if (hashEntry->flag == HFLAG_EXACT)
				return hashEntry->score;
			if (hashEntry->flag == HFLAG_ALPHA && score <= alpha)
				return alpha;
			if (hashEntry->flag == HFLAG_BETA && score >= beta)
				return beta;
		}
	}
	
	return NO_HASH_ENTRY;
}

static inline void recordHash(int depth, int score, int flag)
{
	TransposTable* hashEntry = &tt[hashKey % HASH_SIZE];
	
	if (score < -mateScore) score -= ply;
    if (score > mateScore) score += ply;

	hashEntry->hashKey = hashKey;
	hashEntry->depth = depth;
	hashEntry->score = score;
	hashEntry->flag = flag;
}

static inline int isRepetition()
{
	for (int i = 0; i < repIndex; i++)
		if (hashKey == repTable[i])
			return 1;
	
	return 0;
}

int nnuePieces[12] = { 6, 5, 4, 3, 2, 1, 12, 11, 10, 9, 8, 7 };

int nnueSquares[64] = {
    a1, b1, c1, d1, e1, f1, g1, h1,
	a2, b2, c2, d2, e2, f2, g2, h2,
	a3, b3, c3, d3, e3, f3, g3, h3,
	a4, b4, c4, d4, e4, f4, g4, h4,
	a5, b5, c5, d5, e5, f5, g5, h5,
	a6, b6, c6, d6, e6, f6, g6, h6,
	a7, b7, c7, d7, e7, f7, g7, h7,
	a8, b8, c8, d8, e8, f8, g8, h8
};

static inline int evaluate()
{
	int piece, square;

    uint64_t bitboard;

	int pieces[33];
	int squares[33];

	int index = 2;

    for (int bb_piece = P; bb_piece <= k; bb_piece++)
    {
        bitboard = board[bb_piece];
        
        while (bitboard)
        {
            piece = bb_piece;
            square = getLSB(bitboard);
            
            if (piece == K)
            {
                pieces[0] = nnuePieces[piece];
                squares[0] = nnueSquares[square];
            }
            else if (piece == k)
            {
                pieces[1] = nnuePieces[piece];
                squares[1] = nnueSquares[square];
            }
            else
            {
                pieces[index] = nnuePieces[piece];
                squares[index] = nnueSquares[square];
                index++;
            }

            zeroBit(bitboard, square);
        }
    }

	pieces[index] = 0;
	squares[index] = 0;
	
    return evaluateNNUE(side, pieces, squares) * (100 - fiftyMove) / 100;
}

// score moves
static inline int scoreMove(int move)
{
    if (pvTable[0][ply] == move)
        return 20000;
	
	// score capture
    if (getMoveCapture(move))
    {
        int target_piece = P;
        int start_piece, end_piece;

        if (side == WHITE) { start_piece = p; end_piece = k; }
        else { start_piece = P; end_piece = K; }

        for (int bb_piece = start_piece; bb_piece <= end_piece; bb_piece++)
        {
            if (getBit(board[bb_piece], getMoveTarget(move)))
            {
                target_piece = bb_piece;
                break;
            }
        }
        
        return MVV_LVA[getMovePiece(move)][target_piece] + 10000;
    }
    // score quiet move
    else
    {
        if (killerMoves[0][ply] == move)
            return 9000;
        else if (killerMoves[1][ply] == move)
            return 8000;
        else
            return historyMoves[getMovePiece(move)][getMoveTarget(move)];
    }
    
    return 0;
}

static inline void sortMoves(MoveList *moveList)
{
    int moveScores[moveList->count];

    for (int count = 0; count < moveList->count; count++)
        moveScores[count] = scoreMove(moveList->moves[count]);
    
    for (int current_move = 0; current_move < moveList->count; current_move++)
    {
        for (int next_move = current_move + 1; next_move < moveList->count; next_move++)
        {
            if (moveScores[current_move] < moveScores[next_move])
            {
                int temp_score = moveScores[current_move];
                moveScores[current_move] = moveScores[next_move];
                moveScores[next_move] = temp_score;

                int temp_move = moveList->moves[current_move];
                moveList->moves[current_move] = moveList->moves[next_move];
                moveList->moves[next_move] = temp_move;
            }
        }
    }
}

static inline int quiesce(int alpha, int beta)
{
	nodes++;

	if (!(nodes & 2047))
		communicate();

	if (ply && isRepetition())
		return 0;

	int score = 0;
	int standPat = evaluate();

	if (standPat >= beta)
		return beta;
	if (standPat > alpha)
		alpha = standPat;

	MoveList moveList[1];
	generateCaptures(moveList);
	sortMoves(moveList);

	for (int i = 0; i < moveList->count; i++)
	{
		copyBoard();

		if (!makeMove(moveList->moves[i]))
			continue;
			
		ply++;
		repTable[++repIndex] = hashKey;

		score = -quiesce(-beta, -alpha);

		ply--;
		repIndex--;

		takeBack();
		
		if (stopped) return 0;
		
		if (score >= beta)
			return beta;
		if (score > alpha)
			alpha = score;
	}

	return alpha;
}

static inline int negamax(int depth, int alpha, int beta)
{
	int score = 0;
	int legalMoves = 0;
	int movesSearched = 0;
	int pvNode = beta - alpha > 1;
	int hashFlag = HFLAG_ALPHA;

	pvLength[ply] = ply;
	nodes++;

	if (!(nodes & 2047))
		communicate();

	if (ply && isRepetition() || fiftyMove >= 100)
		return 0;

	if (ply && !pvNode && (score = probeHash(depth, alpha, beta)) != NO_HASH_ENTRY)
		return score;

	if (depth == 0)
		return quiesce(alpha, beta);

	bool inCheck = isSquareAttacked(side == WHITE ? getLSB(board[K]) : getLSB(board[k]), side ^ 1);

	if (inCheck) depth++;

	if (depth >= 3 && ply && !inCheck)
	{
		copyBoard();
		ply++;
		repTable[++repIndex] = hashKey;
		if (enpassant != noSqr) hashKey ^= enpassantKeys[enpassant];
		enpassant = noSqr;
		side ^= 1;
		hashKey ^= sideKey;
		score = -negamax(depth - 3, -beta, -beta + 1);
		ply--;
		repIndex--;
		takeBack();
		if (score >= beta)
			return beta;
	}

	MoveList moveList[1];
	generateMoves(moveList);
	sortMoves(moveList);

	for (int i = 0; i < moveList->count; i++)
	{
		copyBoard();
		
		if (!makeMove(moveList->moves[i]))
			continue;

		legalMoves++;
		ply++;
		
		repTable[++repIndex] = hashKey;

		if (!movesSearched)
			score = -negamax(depth - 1, -beta, -alpha);
		else
		{
			// Late Move Reduction
			if (movesSearched >= 4 && depth >= 3 && !inCheck && !getMoveCapture(moveList->moves[i]) && !getMovePromoted(moveList->moves[i]))
				score = -negamax(depth - 2, -alpha - 1, -alpha);
			else
				score = alpha + 1;
			
			if (score > alpha)
			{
				score = -negamax(depth - 1, -alpha - 1, -alpha);

				if ((score > alpha) && (score < beta))
					score = -negamax(depth - 1, -beta, -alpha);
			}
		}

		ply--;
		repIndex--;

		takeBack();
		
		movesSearched++;

		if (stopped) return 0;

		if (score >= beta)
		{
			recordHash(depth, beta, HFLAG_BETA);
			
			if (!getMoveCapture(moveList->moves[i]))
			{
				killerMoves[1][ply] = killerMoves[0][ply];
				killerMoves[0][ply] = moveList->moves[i];
			}
				
			return beta;
		}

		if (score > alpha)
		{
			hashFlag = HFLAG_EXACT;
		
			alpha = score;

			if (!getMoveCapture(moveList->moves[i]))
				historyMoves[getMovePiece(moveList->moves[i])][getMoveTarget(moveList->moves[i])] += depth;

            pvTable[ply][ply] = moveList->moves[i];
        
            for (int nextPly = ply + 1; nextPly < pvLength[ply + 1]; nextPly++)
                pvTable[ply][nextPly] = pvTable[ply + 1][nextPly];
            
            pvLength[ply] = pvLength[ply + 1];
		}
	}

	if (legalMoves == 0)
	{
		if (inCheck)
			return -49000 + ply;
		else
			return 0;
	}
	
	recordHash(depth, alpha, hashFlag);

	return alpha;
}

void searchPosition(int depth)
{
	int score = 0;
	int alpha = -INF;
	int beta = INF;

	nodes = 0;

	memset(pvTable, 0, sizeof(pvTable));
	memset(pvLength, 0, sizeof(pvLength));
	memset(killerMoves, 0, sizeof(killerMoves));
	memset(historyMoves, 0, sizeof(historyMoves));

	int start = getTimeMS();

	for (int currentDepth = 1; currentDepth <= depth; currentDepth++)
	{
		if (stopped) break;

		score = negamax(currentDepth, alpha, beta);

		if (pvLength[0])
		{
			if (score > -mateValue && score < -mateScore)
                cout << "info score mate " << -(score + mateValue) / 2 - 1 << " depth " << currentDepth << " nodes " << nodes 
					<< " time " << getTimeMS() - start << " pv ";
            else if (score > mateScore && score < mateValue)
                cout << "info score mate " << (mateValue - score) / 2 + 1 << " depth " << currentDepth << " nodes " << nodes 
					<< " time " << getTimeMS() - start << " pv ";
            else
				cout << "info score cp " << score << " depth " << currentDepth << " nodes " << nodes << " time "
					<< getTimeMS() - start << " pv ";

			for (int i = 0; i < pvLength[0]; i++)
				cout << squareToCoords[getMoveSource(pvTable[0][i])] << squareToCoords[getMoveTarget(pvTable[0][i])] << " ";

			cout << endl;
		}
	}

	cout << "bestmove ";
	cout << squareToCoords[getMoveSource(pvTable[0][0])] << squareToCoords[getMoveTarget(pvTable[0][0])] << endl;
}

static inline void perft(int depth)
{
	if (depth == 0)
	{
		nodes++;
		return;
	}

	MoveList moves[1];
	generateMoves(moves);

	for (int i = 0; i < moves->count; i++)
	{
		copyBoard();

		if (!makeMove(moves->moves[i]))
			continue;

		perft(depth - 1);

		takeBack();
	}
}

void parseGo(char *command)
{
	quit = 0;
    movestogo = 30;
    movetime = -1;
    tTime = -1;
    inc = 0;
    starttime = 0;
    stoptime = 0;
    timeset = 0;
    stopped = 0;

    int depth = -1;

    char *argument = NULL;

    if ((argument = strstr(command,"infinite"))) {}

    if ((argument = strstr(command,"binc")) && side == BLACK)
        inc = atoi(argument + 5);

    if ((argument = strstr(command,"winc")) && side == WHITE)
        inc = atoi(argument + 5);

    if ((argument = strstr(command,"wtime")) && side == WHITE)
        tTime = atoi(argument + 6);
        
    if ((argument = strstr(command,"btime")) && side == BLACK)
        tTime = atoi(argument + 6);

    if ((argument = strstr(command,"movestogo")))
        movestogo = atoi(argument + 10);

    if ((argument = strstr(command,"movetime")))
        movetime = atoi(argument + 9);

    if ((argument = strstr(command,"depth")))
        depth = atoi(argument + 6);

    if(movetime != -1)
    {
        tTime = movetime;
        movestogo = 1;
    }

    starttime = getTimeMS();

    depth = depth;

    if(tTime != -1)
    {
        timeset = 1;
        tTime /= movestogo;
        if (tTime > 1500) tTime -= 50;
        stoptime = starttime + tTime + inc;
        if (tTime < 1500 && inc && depth == 64) stoptime = starttime + inc - 50;
    }

    if(depth == -1)
        depth = 64;

    printf("tTime: %d  start: %u  stop: %u  depth: %d  timeset:%d\n",
            tTime, starttime, stoptime, depth, timeset);

    searchPosition(depth);
}

void uciLoop()
{
    setbuf(stdin, NULL);
    setbuf(stdout, NULL);

    char input[2000];

    printf("id name Gizmo\n");
    printf("id author Lancer\n");
    printf("uciok\n");

    while (1)
    {
        memset(input, 0, sizeof(input));

        fflush(stdout);

        if (!fgets(input, 2000, stdin))
            continue;
        if (input[0] == '\n')
            continue;
        if (strncmp(input, "isready", 7) == 0)
        {
            printf("readyok\n");
            continue;
        }
        else if (strncmp(input, "position", 8) == 0)
        {
            parsePosition(input);
            clearHashTable();
        }
        else if (strncmp(input, "ucinewgame", 10) == 0)
        {
            parsePosition("position startpos");
            clearHashTable();
        }
        else if (strncmp(input, "go", 2) == 0)
            parseGo(input);
        else if (strncmp(input, "quit", 4) == 0)
            break;
        else if (strncmp(input, "uci", 3) == 0)
        {
            printf("id name Gizmo\n");
            printf("id author Lancer\n");
            printf("uciok\n");
        }
    }
}

void initAll()
{
	initAttackMasks();
	initSliderAttacks(true);
	initSliderAttacks(false);
	initHashKeys();
	clearHashTable();
	initNNUE("nn-62ef826d1a6d.nnue");
}

int main()
{
	initAll();
	
	uciLoop();

	return 0;
}
