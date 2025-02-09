#include <algorithm>
#include <iostream>
#include <vector>
#include <string>
#include <unordered_map>
#include <cmath>

/* 参考: https://hooktail.org/computer/index.php?QR%CB%A1 */

const double EPS = 1.0e-7;

/* householder法による三重対角化（参考: 『よく分かる数値計算』 https://pub.nikkan.co.jp/book/b10019128.html） */
int householder(std::vector<std::vector<double> > &matrix,
                std::vector<std::vector<double> > &tridiag_m) {
  /* 初期化 */
  tridiag_m.clear();
  tridiag_m.resize(matrix.size());
  for (int i = 0; i < matrix.size(); i++) {
    tridiag_m[i] = matrix[i];
  }

  for (int k = 0; k < tridiag_m.size() - 2; k++) {
    double det = 0;
    for (int m_row = k + 1; m_row < tridiag_m.size(); m_row++) {
      det += tridiag_m[m_row][k] * tridiag_m[m_row][k];
    }
    double s_k = -1 * std::sqrt(det);
    if (tridiag_m[k + 1][k] < 0) s_k *= -1;

    double alpha = std::sqrt(2 * s_k * (s_k - tridiag_m[k + 1][k]));
    if (alpha == 0) {
      continue;
    } 

    std::vector<double> u(tridiag_m.size());
    u[k + 1] = (tridiag_m[k + 1][k] - s_k) / alpha;
    for (size_t u_idx = k + 2; u_idx < u.size(); u_idx++) {
      u[u_idx] = tridiag_m[u_idx][k] / alpha;
    }

    std::vector<double> q(tridiag_m.size());
    q[k] = alpha / 2;
    for (size_t q_idx = k + 1; q_idx < q.size(); q_idx++) {
      q[q_idx] = 0.0;
      for (size_t u_idx = k + 1; u_idx < u.size(); u_idx++) {
        q[q_idx] += tridiag_m[q_idx][u_idx] * u[u_idx];
      }
    }

    std::vector<double> v(tridiag_m.size());
    double beta = 0.0;
    for (size_t uq_idx = k + 1; uq_idx < q.size(); uq_idx++) {
      beta += u[uq_idx] * q[uq_idx];
    }
    v[k] = 2 * q[k];
    for (size_t v_idx = k + 1; v_idx < v.size(); v_idx++) {
      v[v_idx] = 2 * (q[v_idx] - beta * u[v_idx]);
    }

    /* 更新 */
    tridiag_m[k][k + 1] = s_k;
    tridiag_m[k + 1][k] = s_k;
    for (size_t m_idx = k + 2; m_idx < tridiag_m.size(); m_idx++) {
      tridiag_m[m_idx][k] = 0.0;
      tridiag_m[k][m_idx] = 0.0;
    }
    for (size_t m_i = k + 1; m_i < tridiag_m.size(); m_i++) {
      tridiag_m[m_i][m_i] = tridiag_m[m_i][m_i] - 2 * u[m_i] * v[m_i];
      for (size_t m_j = m_i + 1; m_j < tridiag_m.size(); m_j++) {
        tridiag_m[m_i][m_j] = tridiag_m[m_i][m_j] - u[m_i] * v[m_j] - v[m_i] * u[m_j];
        tridiag_m[m_j][m_i] = tridiag_m[m_i][m_j];
      }
    }
  }
  return 0;
};


/* 2 * 2の行列から固有値を取り出し、右下隅の値により近い方を返す  */
double getEigenValue22(std::vector<std::vector<double> > &m, size_t row, size_t col) {
  float b = m[row][col] + m[row + 1][col + 1];
  float det = b * b - 4 * (m[row][col] * m[row + 1][col + 1] - m[row][col + 1] * m[row + 1][col]);
  if (det < 0) det = 0; 
  float eig1 = (b + std::sqrt(det)) / 2;
  float eig2 = (b - std::sqrt(det)) / 2;
  if (std::abs(eig1 - m[row + 1][col + 1]) < std::abs(eig2 - m[row + 1][col + 1])) {
    return eig1;
  } else {
    return eig2;
  }
};

int nextAQ(std::vector<std::vector<double> > &m,
           std::vector<std::vector<double> > &q) {
  for(size_t i = 0; i < q.size() - 1; i++){
    double alpha = std::sqrt(m[i][i] * m[i][i] + m[i + 1][i] * m[i + 1][i]);
    double sin = 0.0;
    double cos = 0.0;
    if (alpha > 0.0) {
      sin = m[i + 1][i] / alpha;
      cos = m[i][i] / alpha;
    }
    for (size_t m_idx = i + 1; m_idx < q.size(); m_idx++) {
      double tmp = -1 * m[i][m_idx] * sin + m[i + 1][m_idx] * cos;
      m[i][m_idx] = m[i][m_idx] * cos + m[i + 1][m_idx] * sin;
      m[i + 1][m_idx] = tmp;
    } 
    for (size_t q_idx = 0; q_idx < q.size(); q_idx++) {
      double tmp = -1 * q[q_idx][i] * sin + q[q_idx][i + 1] * cos;
      q[q_idx][i] = q[q_idx][i] * cos + q[q_idx][i + 1] * sin;
      q[q_idx][i + 1] = tmp;
    }
    m[i][i] = alpha;
    m[i + 1][i] = 0.0;
  }
  return 0;
}

int LUDecomp(std::vector<std::vector<double> > &m,
             std::vector<size_t> &pivot) {
  pivot.clear();
  pivot.reserve(m.size());
  for (size_t i = 0; i < m.size(); i++) {
    pivot[i] = i;
  }

  for (size_t k = 0; k < m.size() - 1; k++) {
    double m_max = std::abs(m[k][k]);
    size_t p_cur = k;
    for (size_t m_row = k + 1; m_row < m.size(); m_row++) {
      if (std::abs(m[m_row][k]) > m_max) {
        m_max = std::abs(m[m_row][k]);
        p_cur = m_row;
      }
    }
    if (p_cur != k) {
      for (size_t m_col = 0; m_col < m.size(); m_col++) {
        double tmp = m[k][m_col];
        m[k][m_col] = m[p_cur][m_col];
        m[p_cur][m_col] = tmp;

        size_t tmp_p = pivot[k];
        pivot[k] = pivot[p_cur];
        pivot[p_cur] = tmp_p;
      }
    }

    for (size_t m_row = k + 1; m_row < m.size(); m_row++) {
      m[m_row][k] /= m[k][k];
      for (size_t m_col = k + 1; m_col < m.size(); m_col++) {
        m[m_row][m_col] -= m[m_row][k] * m[k][m_col]; 
      }
    }
  }
  return 0;
}
int inverseIteration(std::vector<std::vector<double> > &matrix, 
                     std::vector<double> &v,
                     double val) {
  v.clear();
  v.resize(matrix.size(), 1.0);

  std::vector<std::vector<double> > lu(matrix);
  for (size_t lu_idx = 0; lu_idx < matrix.size(); lu_idx++) {
    lu[lu_idx][lu_idx] -=val;
  }

  std::vector<size_t> pivot;
  LUDecomp(lu, pivot);

  for (int iter = 0; iter < 1000; iter++) {
    std::vector<double> v_prev(v);

    for (size_t v_idx = 0; v_idx < v.size(); v_idx++) {
      v[v_idx] = v_prev[pivot[v_idx]];
    }

    for (size_t v_idx = 1; v_idx < v.size(); v_idx++) {
      for (size_t f_idx = 0; f_idx < v_idx; f_idx++) {
        v[v_idx] -= lu[v_idx][f_idx] * v[f_idx];
      }
    }

    for (int v_idx = v.size() - 1; v_idx >= 0; v_idx--) {
      for (size_t b_idx = v_idx + 1; b_idx < lu.size(); b_idx++) {
        v[v_idx] -= lu[v_idx][b_idx] * v[b_idx];
      }
      v[v_idx] /= lu[v_idx][v_idx];
    }

    /* normalize */
    double norm = 0.0;
    for (auto &v_e : v) {
      norm += v_e * v_e;
    }
    norm = std::sqrt(norm);

    for (size_t v_idx = 0; v_idx < v.size(); v_idx++) {
      v[v_idx] /= norm;
    }
    
    /* 収束判定 */
    bool conv_flag = true;
    for (size_t v_idx = 0; v_idx < v.size(); v_idx++) {
      if (std::abs(v_prev[v_idx] - v[v_idx]) > EPS) {
        conv_flag = false;
        break;
      } 
    }
    if (conv_flag) break;
  }
  return 0;
}

int qr(std::vector<std::vector<double> > &matrix, 
       std::vector<std::vector<double> > &e_vec,
       std::vector<double> &e_value) {
  /* 三重対角化 */
  std::vector<std::vector<double> > tridiag_m;
  householder(matrix, tridiag_m);

  size_t now_size = tridiag_m.size();
  while (now_size > 1) {
    if (std::abs(tridiag_m[now_size - 1][now_size - 2]) < EPS) {
      now_size--;
      continue;
    }
    double mu = getEigenValue22(tridiag_m, now_size - 2, now_size - 2);
    for (size_t m_idx = 0; m_idx < now_size; m_idx++) {
      tridiag_m[m_idx][m_idx] -= mu;
    }

    std::vector<std::vector<double> > q(now_size);
    for (size_t i = 0; i < now_size; i++) {
      q[i].resize(now_size, 0.0);
      q[i][i] = 1.0;
    }

    nextAQ(tridiag_m, q);

    /* A = RQ */
    for (size_t m_row = 0; m_row < now_size; m_row++){
      std::vector<double> v(now_size);
			for (size_t q_col = 0; q_col < now_size; q_col++){
  			double sum = 0.0;
				for (size_t k = m_row; k < now_size; k++){
					sum += tridiag_m[m_row][k] * q[k][q_col];
				}
				v[q_col] = sum;
			}
			for (size_t m_col = 0; m_col < now_size; m_col++){
				tridiag_m[m_row][m_col] = v[m_col];
			}
		}

    /* 対角成分にμを戻す */
    for (size_t m_idx = 0; m_idx < now_size; m_idx++) {
      tridiag_m[m_idx][m_idx] += mu;
    }
  }

  e_value.clear();
  e_vec.clear();
  for (size_t m_idx = 0; m_idx < tridiag_m.size(); m_idx++) {
    if (std::abs(tridiag_m[m_idx][m_idx]) < EPS) continue;
    e_value.push_back(tridiag_m[m_idx][m_idx]);
    /* 逆反復法 */
    std::vector<double> v;
    inverseIteration(matrix, v, tridiag_m[m_idx][m_idx]);
    e_vec.emplace_back(v);
  }
  return 0;
};



int main () {
  std::vector<std::vector<double> > m;

  size_t dim = 512;
  m.resize(dim);
  for(size_t i = 0; i < dim; i++){
		for(size_t j = 0; j < dim; j++){
      m[i].push_back(std::log((double)((i + j) % 7 + 1.5)));
      // std::cout << m[i][j] << ", ";
    }
    // std::cout << std::endl;
  }
  // std::cout << std::endl;

  std::vector<std::vector<double> > eigen_vec;
  std::vector<double> eigen_value;
  qr(m, eigen_vec, eigen_value);
  // for(size_t i = 0; i < eigen_vec.size(); i++){
	// 	for(size_t j = 0; j < eigen_vec[i].size(); j++){
  //     printf("%8.8e", eigen_vec[i][j]);
  //     std::cout << ", ";
  //   }
  //   std::cout << std::endl;
  // }
  std::cout << std::endl;
  for (auto f :eigen_value) {
    printf("%8.8e", f);
    std::cout << ", ";
  }
  std::cout << std::endl;
  return 0;
}