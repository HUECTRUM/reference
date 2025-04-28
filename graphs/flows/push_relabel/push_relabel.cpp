#include <bits/stdc++.h>
using namespace std;

struct PushRelabel {
    struct Edge {
        int to, rev, cap, flow;
    };
    int n, s, t;
    vector<vector<Edge>> graph;
    vector<int> excess, height, cur;

    PushRelabel(int n, int s, int t) : n(n), s(s), t(t) {
        graph.resize(n);
        excess.assign(n, 0);
        height.assign(n, 0);
        cur.assign(n, 0);
    }

    inline void addEdge(int u, int v, int cap) {
        graph[u].push_back({v, (int)graph[v].size(), cap, 0});
        graph[v].push_back({u, (int)graph[u].size()-1, 0, 0});
    }

    int maxFlow() {
        height[s] = n;
        for(auto &e : graph[s]) {
            int delta = e.cap;
            if(delta > 0) {
                e.cap = 0;
                graph[e.to][e.rev].cap += delta;
                e.flow += delta;
                excess[e.to] += delta;
                excess[s] -= delta;
            }
        }
        deque<int> q;
        for (int i = 0; i < n; i++) {
            if(i != s && i != t && excess[i] > 0)
                q.push_back(i);
        }
        while(!q.empty()){
            int u = q.front();
            q.pop_front();
            int oldHeight = height[u];
            discharge(u, q);
            if(excess[u] > 0) {
                if(height[u] > oldHeight)
                    q.push_front(u);
                else
                    q.push_back(u);
            }
        }
        return excess[t];
    }

    inline void discharge(int u, deque<int>& q) {
        while(excess[u] > 0) {
            if(cur[u] < (int)graph[u].size()) {
                auto &e = graph[u][cur[u]];
                if(e.cap > 0 && height[u] == height[e.to] + 1) {
                    int delta = min(excess[u], e.cap);
                    e.cap -= delta;
                    graph[e.to][e.rev].cap += delta;
                    e.flow += delta;
                    graph[e.to][e.rev].flow -= delta;
                    excess[u] -= delta;
                    excess[e.to] += delta;
                    if(e.to != s && e.to != t && excess[e.to] == delta)
                        q.push_back(e.to);
                } else {
                    cur[u]++;
                }
            } else {
                relabel(u);
                cur[u] = 0;
            }
        }
    }

    inline void relabel(int u) {
        int minHeight = INT_MAX;
        for(auto &e : graph[u])
            if(e.cap > 0)
                minHeight = min(minHeight, height[e.to]);
        if(minHeight < INT_MAX)
            height[u] = minHeight + 1;
    }
};
