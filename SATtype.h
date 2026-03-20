#include <iostream>
#include <vector>
enum class lbool
{
    l_true = 0,
    l_false = 1,
    l_undef = 2
};
typedef int Lit; // 文字
inline Lit locateLit(int var, bool is_neg)
{
    return (var << 1) + ((int)is_neg);
}
inline int getLitId(Lit lit)
{
    return lit >> 1;
}
inline bool isNeg(Lit lit)
{
    return lit & 1;
}
inline Lit getNotLit(Lit lit)
{
    return lit ^ 1;
}
class Clause;
class VarData
{
public:
    lbool value;    // 赋值的真值
    int level;      // 如果是决策赋值，由哪个决策层级推导出的？
    Clause *reason; // 如果是由子句推导赋值，由哪个子句推导出的？
    VarData() : value(lbool::l_undef), level(-1), reason(nullptr)
    {
    }
};
class Clause
{
public:
    std::vector<Lit> lits;
    bool learnt;
    Clause(const std::vector<Lit> &_lits, bool _learnt) : lits(_lits), learnt(_learnt)
    {
        // 用常量初始化防止修改
    }
};
