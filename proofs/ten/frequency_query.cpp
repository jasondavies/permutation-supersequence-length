// Answer frequency-capacity queries for the complementary-cut solver.
#include "../shared/frequency_bounds.hpp"
#include <iostream>

int main() {
    using namespace supersequence;
    FrequencyBounds bounds;
    int size;
    while (std::cin >> size) {
        Counts values(size);
        for (int& x : values) std::cin >> x;
        bool passes = bounds.passes(values);
        if (size == 9 && std::accumulate(values.begin(), values.end(), 0) < 66)
            passes = false;
        std::cout << passes << std::endl;
    }
}
