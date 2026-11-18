# Hub remote browser (run on Render as "Docker")
FROM node:20-bookworm-slim
# Chromium + Japanese fonts (Noto CJK) + emoji
RUN apt-get update \
 && apt-get install -y --no-install-recommends chromium fonts-noto-cjk fonts-noto-color-emoji ca-certificates dumb-init \
 && rm -rf /var/lib/apt/lists/*
ENV CHROME_PATH=/usr/bin/chromium NODE_ENV=production
WORKDIR /app
COPY package.json ./
RUN npm install --omit=dev --no-audit --no-fund
COPY server.js ./
RUN useradd -m rb && chown -R rb /app
USER rb
EXPOSE 10000
ENTRYPOINT ["dumb-init", "--"]
CMD ["node", "server.js"]
