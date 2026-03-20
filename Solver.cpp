#define _CRT_SECURE_NO_WARNINGS 1
#include "SATtype.h"
#include <cstdio>
#include <chrono>

class Solver
{
	/*
	变量编号   0     1     2      3  （这是在vars数组中的下标）
	对应lit  0   1 2   3 4   5  6   7



	*/

public:
	int conflicts = 0;			 // 记录自上次重启以来的冲突次数
	int restart_inc = 100;		 // 初始重启阈值（每100次冲突重启一次）
	int restart_limit = 100;	 // 当前重启阈值
	double restart_growth = 1.1; // 阈值增长因子（防止重启过于频繁）
	double var_inc = 1.0;		 // 每次增加的活跃。
	double var_decay = 0.95;
	void varDecayActiviy()
	{
		var_inc *= (1.0 / var_decay);
	}
	void varBumpActivity(int var)
	{
		activity[var] += var_inc;

		// 防止 double 溢出：如果某个变量的分数大到离谱，就把所有人的分数缩小
		if (activity[var] > 1e100)
		{
			for (int i = 0; i < vars.size(); i++)
			{
				activity[i] *= 1e-100;
			}
			var_inc *= 1e-100;
		}
	}
	std::vector<bool> seen;
	std::vector<Lit> trail; // 轨迹栈，记录被赋值后，需要传播的变量
	std::vector<VarData> vars;
	std::vector<Clause *> clauses;
	std::vector<std::vector<Clause *>> watchers; // watchers[lit]表示在监视lit文字的子句列表
	int qhead = 0;								 // 传播栈trail中，待处理的那个赋值。
	int newVar()
	{						 // 增加一个变量，同时把watchers对应位置填充
		int v = vars.size(); // 记录当前的变量数量
		vars.push_back(VarData());
		watchers.push_back(std::vector<Clause *>());
		watchers.push_back(std::vector<Clause *>());
		seen.push_back(false);
		activity.push_back(0.0);
		phases.push_back(false);
		return v; // 返回新变量的下标
	}
	void addClause(const std::vector<Lit> lits)
	{
		if (lits.empty())
		{
			printf("empty lits!\n");
			return;
		}
		if (lits.size() == 1)
		{

			assign(lits[0]); // 单子句的文字必定为true
			return;
		}
		Clause *c = new Clause(lits, false);
		clauses.push_back(c);
		// 初始化时，我们监视前两个文字
		watchers[getNotLit(lits[0])].push_back(c);
		watchers[getNotLit(lits[1])].push_back(c);
		// 取反，所以当一个文字变为真时，其取反变假。通知其下所有子句。
	}
	bool parse_DIMACS(const char *filename)
	{
		FILE *f = fopen(filename, "r");
		if (!f)
		{
			printf("fail to read file\n");
			return false;
		}
		int num_vars = 0;
		int num_clauses = 0;
		char line_buf[1024];
		while (fscanf(f, " %c", line_buf) != EOF)
		{
			if (line_buf[0] == 'c')
			{
				// 跳过注释行
				fgets(line_buf, sizeof(line_buf), f);
			}
			else if (line_buf[0] == 'p')
			{
				// 读取 p cnf vars clauses
				fscanf(f, " cnf %d %d", &num_vars, &num_clauses);
				for (int i = 0; i < num_vars; i++)
					newVar(); // 创建所有的变量
			}
			else
			{
				// 读取子句：数字以 0 结束
				ungetc(line_buf[0], f); // 把读出来的字符塞回去
				std::vector<Lit> lits;
				int val;
				while (fscanf(f, "%d", &val) == 1 && val != 0)
				{
					int var_idx = abs(val) - 1; // DIMACS 从 1 开始，我们从 0 开始
					lits.push_back(locateLit(var_idx, val < 0));
				}
				addClause(lits);
			}
		}
		fclose(f);
		printf("finish parsing: %d variables, %d clauses which are not single\n", (int)vars.size(), (int)clauses.size());
		return true;
	}
	void printClauses()
	{ // just for debugging
		printf("clauses: %zu  ---\n", clauses.size());
		for (size_t i = 0; i < clauses.size(); i++)
		{
			printf("clause [%zu]: ", i);
			Clause *c = clauses[i];
			for (size_t j = 0; j < c->lits.size(); j++)
			{
				Lit p = c->lits[j];
				int var_id = getLitId(p) + 1; // 还原回从 1 开始的编号
				if (isNeg(p))
				{
					printf("-%d ", var_id);
				}
				else
				{
					printf("%d ", var_id);
				}
			}
			printf("0\n"); // DIMACS 格式每行以 0 结尾
		}
		printf("--------------------------------\n");
	}
	void assign(Lit lit, Clause *reason = nullptr)
	{
		// 将文字lit设置为true，将其对应的变量设置为true或者false，并记录这个变量的决策来历。

		int var = getLitId(lit);
		if (vars[var].value != lbool::l_undef)
		{
			printf("UNSAT\n"); // 对一个已经赋值的变量赋值，必然是两个矛盾的单子句造成。
			// 注意我们的cancel回退时，不是通过assign函数重新赋值变量的，而是直接操作变量回退的。
			exit(0);
		}
		vars[var].value = isNeg(lit) ? lbool::l_false : lbool::l_true;
		vars[var].reason = reason;
		vars[var].level = decisionLevel();
		phases[var] = !isNeg(lit);
		trail.push_back(lit); // 放入传播栈
	}
	lbool value(Lit lit) const
	{
		// 给一个文字，求其在当前赋值下的取值
		int v = getLitId(lit);
		lbool vv = vars[v].value;
		if (vv == lbool::l_undef)
			return lbool::l_undef;
		if (vv == lbool::l_true)
		{
			return isNeg(lit) ? lbool::l_false : lbool::l_true;
		}
		if (vv == lbool::l_false)
		{
			return isNeg(lit) ? lbool::l_true : lbool::l_false;
		}
	}
	Clause *propagate()
	{
		Clause *conflict = nullptr;
		// 传播：取出trail中，当前qhead所指向的那个赋值，找出监视它的所有子句，进行更新。
		while (qhead < trail.size())
		{
			Lit p = trail[qhead];
			qhead++;
			Lit false_lit = getNotLit(p); // false_lit才是变为false的那个
			// p是被赋值为真的。由于前面将监视p的子句挂载到not p下，所以这里直接用p作为下标即可取出。
			std::vector<Clause *> &ws = watchers[p]; // 获得监视not p的列表
			for (int i = 0; i < ws.size();)
			{
				Clause &c = *ws[i]; // 取出列表中的子句
				if (c.lits[0] == false_lit)
				{
					std::swap(c.lits[0], c.lits[1]);
				}
				// 这样操作后，c.lits[1]就是被赋值为false的文字，而c.lits[0]是另一个监视文字.
				if (value(c.lits[0]) == lbool::l_true)
				{
					// 另一个文字是true，没有推导的机会。
					i++;
					continue;
				}
				// 否则，另一个文字是undef或者true，尝试寻找一个文字，代替lits[1]。
				bool found_new = false;
				for (int k = 2; k < c.lits.size(); k++)
				{
					if (value(c.lits[k]) != lbool::l_false)
					{
						// 找到不为false的
						c.lits[1] = c.lits[k];
						c.lits[k] = false_lit;
						// 然后更新watchers
						watchers[getNotLit(c.lits[1])].push_back(&c);
						// 原来监视的文字的watchers列表也要删除掉这个子句
						// ws就是原来监视的文字的watchers，i处的子句就是要删除的子句。
						ws[i] = ws.back();
						ws.pop_back();
						// 某个文字的监视子句列表中，子句的顺序是不重要的。
						found_new = true;
						break;
					}
				}
				if (found_new)
				{
					continue; // 找到了可替代的，当前子句传播完成。
							  // i++不能自增，因为后面的替代子句和当前子句交换了位置，并且当前子句被删除了。
				}
				// 没找到可替代的，那么看lits0是不是false
				if (value(c.lits[0]) == lbool::l_false)
				{
					// 发生冲突
					conflict = &c;
					qhead = trail.size(); // 停止传播，处理冲突
					break;
				}
				else
				{
					// lits0是undef，那么可以推导,依据为子句c
					assign(c.lits[0], &c);
					i++;
				}
			}
		}
		return conflict;
	}
	std::vector<int> trail_lim;
	int decisionLevel() const
	{
		return trail_lim.size();
	}
	void newDecisionLevel()
	{
		// 将当前的长度存入trail
		trail_lim.push_back(trail.size());
	}
	void cancel(int level)
	{
		// 得到当前的决策层
		// trail_lim[0]:第1层决策的文字，在trail中的下标
		// trail_lim[n]:第n+1层决策的文字，在trail中的下标 
		int nowlevel = decisionLevel();
		if (nowlevel > level)
		{
			int limit = trail_lim[level]; // 这是第level+1层决策的文字在trail中的下标。
			for (int i = trail.size() - 1; i >= limit; i--)
			{
				vars[getLitId(trail[i])].value = lbool::l_undef;
				vars[getLitId(trail[i])].level = -1;
				vars[getLitId(trail[i])].reason = nullptr;
				// 回退第level+1层以及以后的决策。
			}
			trail.resize(limit);
			trail_lim.resize(level); // 全部回退到第level层决策刚做完之后的情况
			// 现在trail_lim.back就是第level层的最后一个变量，在trail中的下标
			qhead = limit;
		}
	}
	Lit pickBranchLit()
	{
		int best_var = -1;
		double max_activity = -1.0;

		// 遍历所有变量，寻找未赋值且活跃度最高的变量
		for (int i = 0; i < vars.size(); i++)
		{
			if (vars[i].value == lbool::l_undef)
			{
				if (best_var == -1 || activity[i] > max_activity)
				{
					best_var = i;
					max_activity = activity[i];
				}
			}
		}

		if (best_var == -1)
			return -1; // 所有变量已赋值

		auto last_phase = phases[best_var];
		return locateLit(best_var, !last_phase); // 保持和上一次一致。
	}

	void analyze(Clause *conflict, std::vector<Lit> &Outlearn, int &backlevel)
	{
		int catchedLitsnum = 0; // 当前正在被分析的，当前决策层级的文字数量。
		int p = -1;				// 决定从trail[p]文字开始向前推导
		int index = trail.size() - 1;
		Outlearn.push_back(-1); // 学习子句的0位置存放1stUIP。
		do
		{
			Clause &c = *conflict; // 拿出用来推导的子句
			// 断言：子句c中的所有文字都被赋值了，因为c要么是冲突子句，要么是用来推导的子句。
			for (int i = (p == -1 ? 0 : 1); i < c.lits.size(); i++)
			{
				Lit lit = c.lits[i]; // 取得当前的文字
				int var = getLitId(lit);
				if (vars[var].level > 0 && !seen[var])
				{
					// 发现子句中需要处理的变量

					seen[var] = true;
					varBumpActivity(var);
					if (vars[var].level < decisionLevel())
					{
						// 对于不属于当前层的文字，一定在学习子句中
						Outlearn.push_back(lit);
					}
					else
					{
						catchedLitsnum++;
					}
				}
			}
			while (!seen[getLitId(trail[index])])
			{
				index--;
			}
			// 找到当前需要处理的那个文字
			p = trail[index];
			conflict = vars[getLitId(p)].reason;
			seen[getLitId(p)] = false; //
			catchedLitsnum--;
			index--;

		} while (catchedLitsnum);
		Outlearn[0] = getNotLit(p);
		if (Outlearn.size() == 1)
		{
			backlevel = 0;
		}
		else
		{
			int max_i = 1; // 设定为下标1是最大的。可以从下标2开始遍历
			for (int i = 2; i < Outlearn.size(); i++)
			{
				if (vars[getLitId(Outlearn[i])].level > vars[getLitId(Outlearn[max_i])].level)
				{
					max_i = i;
				}
			}
			std::swap(Outlearn[1], Outlearn[max_i]); // 将最高等级的放到lits[1]的位置
			backlevel = vars[getLitId(Outlearn[1])].level;
		}
		for (Lit l : Outlearn)
			seen[getLitId(l)] = false;
		varDecayActiviy();
	}
	lbool solve()
	{

		while (true)
		{
			Clause *conflict = propagate();

			if (conflict != nullptr)
			{
				// --- 冲突处理 ---
				conflicts++;
				if (decisionLevel() == 0)
					return lbool::l_false; // 根层冲突，无解

				std::vector<Lit> learnt_clause;
				int backtrack_level;
				analyze(conflict, learnt_clause, backtrack_level);

				// 回跳到计算出的层级
				cancel(backtrack_level);
				bool restart = false;
				if (conflicts >= restart_limit)
				{
					// 回退到 Level 0 (根层)，清空所有当前赋值
					restart = true;
					cancel(0);

					// 调整下一次重启的阈值
					conflicts = 0;
					restart_limit = (int)(restart_limit * restart_growth);

					// 打印信息观察进度（可选）
					printf("Restarting... next limit: %d\n", restart_limit);
				}
				if (learnt_clause.size() == 1)
				{
					// 学习到单子句，它在 Level 0 以后永远为真
					assign(learnt_clause[0]);
				}
				else
				{
					// 学习到普通子句
					Clause *c = new Clause(learnt_clause, true);
					clauses.push_back(c);
					// Outlearn[0]是1st UIP，Outlearn[1]是回跳层级文字
					watchers[getNotLit(learnt_clause[0])].push_back(c);
					watchers[getNotLit(learnt_clause[1])].push_back(c);

					if (!restart)
					{
						// 回退后手动赋值，不用传播寻找
						assign(learnt_clause[0], c);
					}
				}
			}
			else
			{
				// --- 决策分支 ---
				Lit next = pickBranchLit();
				if (next == -1)
					return lbool::l_true; // 所有变量已赋值，说明SAT
				newDecisionLevel();
				assign(next);
			}
		}
	}
	std::vector<double> activity; // 每个变量的活跃度
	std::vector<bool> phases;
};

int main()
{
	auto solver = Solver();
	solver.parse_DIMACS("testunsat.cnf");
	auto start = std::chrono::high_resolution_clock::now();
	lbool ans = solver.solve();
	auto end = std::chrono::high_resolution_clock::now();
	std::chrono::duration<double, std::milli> elapsed = end - start;
	if (ans == lbool::l_true)
	{
		printf("\nSAT\n");
	}
	else
	{
		printf("\nUNSAT\n");
	}
	printf("time cost: %.2f ms\n", elapsed.count());
	return 0;
}
