#include <iostream>
#include <vector>
#include <fstream>
#include <cmath>
#include <string>

using namespace std;

int getVar(int r, int c, int N)
{
    return r * N + c + 1;
}

void generateQueensCNF(int N)
{
    if (N < 1)
        return;

    vector<vector<int>> clauses;

    for (int i = 0; i < N; ++i)
    {
        vector<int> clause;
        for (int j = 0; j < N; ++j)
            clause.push_back(getVar(i, j, N));
        clauses.push_back(clause);
    }

    for (int i = 0; i < N; ++i)
    {
        for (int j = 0; j < N; ++j)
        {
            for (int k = j + 1; k < N; ++k)
            {
                clauses.push_back({-getVar(i, j, N), -getVar(i, k, N)});
            }
        }
    }

    for (int j = 0; j < N; ++j)
    {
        for (int i = 0; i < N; ++i)
        {
            for (int k = i + 1; k < N; ++k)
            {
                clauses.push_back({-getVar(i, j, N), -getVar(k, j, N)});
            }
        }
    }

    for (int r1 = 0; r1 < N; ++r1)
    {
        for (int c1 = 0; c1 < N; ++c1)
        {
            for (int r2 = 0; r2 < N; ++r2)
            {
                for (int c2 = 0; c2 < N; ++c2)
                {

                    if (getVar(r1, c1, N) < getVar(r2, c2, N))
                    {

                        if (abs(r1 - r2) == abs(c1 - c2))
                        {
                            clauses.push_back({-getVar(r1, c1, N), -getVar(r2, c2, N)});
                        }
                    }
                }
            }
        }
    }

    // 写入文件
    string fileName = std::to_string(N) + "queens.cnf";
    ofstream outfile(fileName);

    if (!outfile.is_open())
    {
        cout << "fail to create file" << endl;
        return;
    }

    outfile << "c " << N << "-Queens Problem\n";
    outfile << "c Variables: 1 to " << N * N << " (row * N + col + 1)\n";
    outfile << "p cnf " << N * N << " " << clauses.size() << "\n";

    for (const auto &clause : clauses)
    {
        for (int lit : clause)
        {
            outfile << lit << " ";
        }
        outfile << "0\n";
    }

    outfile.close();
    cout << "successfully save file as: " << fileName << endl;
    cout << "variables: " << N * N << " | clause: " << clauses.size() << endl;
}

int main()
{
    int n;
    cout << "N: ";
    if (!(cin >> n))
    {
        cout << "error" << endl;
        return 1;
    }

    generateQueensCNF(n);
    return 0;
}