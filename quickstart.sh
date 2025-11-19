#!/bin/bash

echo "=================================================="
echo "SMT-LIB Pipeline Service - Quick Start"
echo "=================================================="
echo ""

# Check if .env exists
if [ ! -f .env ]; then
    echo "⚠️  No .env file found. Creating from .env.example..."
    cp .env.example .env
    echo "✅ Created .env file"
    echo ""
    echo "⚠️  IMPORTANT: Edit .env and add your ANTHROPIC_API_KEY"
    echo ""
    read -p "Press Enter after you've added your API key to .env..."
fi

# Check if poetry is installed
if ! command -v poetry &> /dev/null; then
    echo "❌ Poetry not found. Please install it first:"
    echo "   curl -sSL https://install.python-poetry.org | python3 -"
    exit 1
fi

echo "📦 Installing dependencies with Poetry..."
poetry install

echo ""
echo "🧪 Testing imports..."
poetry run python test_imports.py

if [ $? -eq 0 ]; then
    echo ""
    echo "=================================================="
    echo "✅ Setup Complete!"
    echo "=================================================="
    echo ""
    echo "To start the service, run:"
    echo "  poetry run python -m src.main"
    echo ""
    echo "Or use uvicorn directly:"
    echo "  poetry run uvicorn src.main:app --reload"
    echo ""
    echo "Then open your browser to:"
    echo "  http://localhost:8000/docs"
    echo ""
else
    echo ""
    echo "❌ Import test failed. Please check the error messages above."
    exit 1
fi
