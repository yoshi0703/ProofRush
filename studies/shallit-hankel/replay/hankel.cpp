#include <cstdint>
#include <cstdlib>
#include <iostream>
#include <vector>

using Word = std::uint64_t;
constexpr Word modulus = (Word{1} << 61) - 1;

Word multiply(Word x, Word y) {
    __uint128_t product = __uint128_t{x} * y;
    Word reduced = Word(product & modulus) + Word(product >> 61);
    return reduced < modulus ? reduced : reduced - modulus;
}

Word subtract(Word x, Word y) {
    return x >= y ? x - y : modulus - y + x;
}

Word inverse(Word value) {
    Word result = 1;
    for (Word power = modulus - 2; power; power >>= 1) {
        if (power & 1) result = multiply(result, value);
        value = multiply(value, value);
    }
    return result;
}

std::vector<Word> fixed_point(std::size_t length) {
    const Word first[] = {0, 1, 2, 1, 3};
    const Word second[] = {0, 2, 3, 4, 2};
    std::vector<Word> sequence(length, 1);
    for (std::size_t index = 1; index < length; ++index) {
        Word parent = sequence[index / 2];
        sequence[index] = index % 2 ? second[parent] : first[parent];
    }
    return sequence;
}

int main(int argc, char** argv) {
    if (argc != 2) return 2;
    std::size_t length = std::strtoull(argv[1], nullptr, 10);
    if (length < 1) return 2;

    std::vector<Word> previous(length, 1);
    std::vector<Word> current = fixed_point(length);
    std::vector<Word> next(length);
    std::vector<Word> products(length);
    std::uint64_t count = length;
    Word checksum = 0;
    for (Word entry : current) checksum = (checksum + entry) % modulus;
    for (std::size_t order = 2; order <= (length + 1) / 2; ++order) {
        std::size_t shifts = length - 2 * order + 2;
        if (order > 2) {
            products[0] = 1;
            for (std::size_t offset = 0; offset < shifts; ++offset) {
                products[offset + 1] = multiply(products[offset], previous[offset + 2]);
            }
        }
        Word reciprocal = order == 2 ? 1 : inverse(products[shifts]);
        for (std::size_t offset = shifts; offset-- > 0;) {
            Word numerator = subtract(multiply(current[offset], current[offset + 2]),
                                     multiply(current[offset + 1], current[offset + 1]));
            next[offset] = order == 2 ? numerator : multiply(numerator, multiply(reciprocal, products[offset]));
            if (next[offset] == 0) {
                std::cout << "zero residue at offset " << offset << " and order " << order << '\n';
                return 1;
            }
            if (order > 2) reciprocal = multiply(reciprocal, previous[offset + 2]);
            checksum = (checksum + next[offset]) % modulus;
        }
        count += shifts;
        previous.swap(current);
        current.swap(next);
    }
    std::cout << "length=" << length << " count=" << count << " checksum=" << checksum
              << " modulus=" << modulus << '\n';
}
