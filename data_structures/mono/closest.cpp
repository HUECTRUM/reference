#include <bits/stdc++.h>
using namespace std;


struct ClosestComp {
    template<typename T> vector<T> findClosest(vector<T> v, auto handler, bool rev = false) {
        int n = v.size();
        stack<T> st;
        if (!rev) {
            vector<T> ans(n, -1);
            for (int i = 0; i < n; ++i) {
                int el = v[i];
                while (st.size() && !handler(v[st.top()], el)) st.pop();

                if (st.size()) ans[i] = st.top();
                st.push(i);
            }
            return ans;
        } else {
            vector<T> ans(n, n);
            for (int i = n - 1; i >= 0; --i) {
                int el = v[i];
                while (st.size() && !handler(v[st.top()], el)) st.pop();

                if (st.size()) ans[i] = st.top();
                st.push(i);
            }
            return ans;
        }
    }
} cc;

int op(int x, int y) {
    return x < y;
}
